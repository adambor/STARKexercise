import {FiniteField, Vector} from "@guildofweavers/galois";
import {ProofStream} from "../fiatshamir/ProofStream";
import {bigIntToBuffer, bufferToBigInt, MerkleTree} from "../merkle/MerkleTree";
import * as crypto from "crypto";
import {Polynomial} from "../polynomial/Polynomial";
import exp from "constants";


export class Fri {

    offset: bigint;
    omega: bigint;
    domainLength: number;
    field: FiniteField;
    expansionFactor: number;
    numColinearityTests: number;

    constructor(
        offset: bigint,
        omega: bigint,
        domainLength: number,
        field: FiniteField,
        expansionFactor: number,
        numColinearityTests: number
    ) {
        this.offset = offset;
        this.omega = omega;
        this.domainLength = domainLength;
        this.field = field;
        this.expansionFactor = expansionFactor;
        this.numColinearityTests = numColinearityTests;
    }

    numRounds(): number {
        let codewordLength = this.domainLength;
        let numRounds = 0;
        while(codewordLength>this.expansionFactor && 4*this.numColinearityTests<codewordLength) {
            codewordLength = codewordLength >> 1;
            numRounds++;
        }
        return numRounds;
    }

    evaluateDomain(): bigint[] {
        return this.field.getPowerSeries(this.omega, this.domainLength).toValues().map(val => this.field.mul(val, this.offset));
    }

    prove(codeword: bigint[], proofStream: ProofStream, byteLength: number): number[] {
        if(this.domainLength!==codeword.length) throw new Error("Invalid codeword length");

        const codewords = this.commit(codeword, proofStream, byteLength);

        const initialIndices = this.sampleIndices(
            proofStream.proverFiatShamir(),
            codewords[1].leafs.length,
            codewords[codewords.length-1].leafs.length,
            this.numColinearityTests
        );

        const indices = Array.from(initialIndices);

        for(let i=0; i<codewords.length-1; i++) {
            const codewordHalf = codewords[i].leafs.length / 2;
            indices.forEach((val, index, arr) => {
                arr[index] = val % codewordHalf;
            });
            this.query(codewords[i], codewords[i+1], indices, proofStream, byteLength);
        }

        return initialIndices;
    }

    commit(codeword: bigint[], proofStream: ProofStream, byteLength: number): MerkleTree[] {

        const two = 2n;
        const twoInverse = this.field.inv(two);
        let offset = this.offset;
        let omega = this.omega;

        const codewordTrees: MerkleTree[] = [];

        const rounds = this.numRounds();

        for(let i=0;i<rounds;i++) {
            const start = Date.now();

            console.log("Start fri round: ", i);

            const pmt = new MerkleTree(codeword, byteLength);
            console.log("Merkle tree computed: ", Date.now()-start);

            const root = pmt.commit();
            proofStream.push(root);

            codewordTrees.push(pmt);

            console.log("PMT committed: ", i);

            //Halt soon on last round
            if(i===rounds-1) break;

            const alpha = this.field.prng(proofStream.proverFiatShamir());

            console.log("Alpha sampled: ", alpha);

            /*
            Split and fold
            2^-1 *
            (
                (1 + a*ω^-i) * f(ω^i) +
                (1 - a*ω^-1) * f(ω^(N/2 + i))
            )
             */

            let omegaPow = 1n;
            const codewordHalfLength = codeword.length/2;
            const newCodeword = Array<bigint>(codewordHalfLength);
            for(let j=0;j<codewordHalfLength;j++) {
                const alphaOmega = this.field.div(alpha, this.field.mul(offset, omegaPow));

                omegaPow = this.field.mul(omegaPow, omega);

                const left = this.field.mul(
                    this.field.add(1n, alphaOmega),
                    codeword[j]
                );
                const right = this.field.mul(
                    this.field.sub(1n, alphaOmega),
                    codeword[codewordHalfLength + j]
                );

                newCodeword[j] = this.field.mul(
                    twoInverse,
                    this.field.add(left, right)
                );
            }

            console.log("FRI folded: ", Date.now()-start);

            codeword = newCodeword;

            omega = this.field.mul(omega, omega);
            offset = this.field.mul(offset, offset);

            console.log("Finish fri round: ", i);
        }

        //Send last codeword
        proofStream.pushBigInts(codeword, byteLength);

        return codewordTrees;

    }

    query(currentCodeword: MerkleTree, nextCodeword: MerkleTree, cIndices: number[], proofStream: ProofStream, byteLength: number): void {
        const halfCurrentCodeword = currentCodeword.leafs.length/2;

        for(let i=0;i<cIndices.length;i++) {
            proofStream.push(bigIntToBuffer(currentCodeword.leafs[cIndices[i]], byteLength));
            proofStream.push(Buffer.concat(currentCodeword.open(cIndices[i])));

            proofStream.push(bigIntToBuffer(currentCodeword.leafs[cIndices[i] + halfCurrentCodeword], byteLength));
            proofStream.push(Buffer.concat(currentCodeword.open(cIndices[i] + halfCurrentCodeword)));

            proofStream.push(bigIntToBuffer(nextCodeword.leafs[cIndices[i]], byteLength));
            proofStream.push(Buffer.concat(nextCodeword.open(cIndices[i])));
        }
    }

    sampleIndices(seed: Buffer, initialSize: number, foldedSize: number, numTests: number): number[] {
        if(numTests > 2*foldedSize) throw new Error("Not enough entropy");
        if(numTests > foldedSize) throw new Error("Not enough points to sample");

        const reducedIndices = new Set<number>();
        const indices = [];
        let counter = 0;

        while(indices.length<numTests) {
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(counter, 0, 6);
            const index = Number(this.field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    seed,
                    counterBuffer
                ])).digest()
            ) % BigInt(initialSize));
            const reducedIndex = index % foldedSize;

            if(!reducedIndices.has(reducedIndex)) {
                reducedIndices.add(reducedIndex);
                indices.push(index);
            }

            counter++;
        }

        return indices;

    }

    verify(proofStream: ProofStream, byteLength: number, polynomialCommitment?: Buffer): bigint[][] {

        let offset = this.offset;
        let omega = this.omega;

        const rounds = this.numRounds();
        const roots: Buffer[] = Array<Buffer>(rounds);
        const alphas: bigint[] = Array<bigint>(rounds);
        for(let i=0;i<rounds;i++) {
            roots[i] = proofStream.pull();
            alphas[i] = this.field.prng(proofStream.verifierFiatShamir());
        }

        if(polynomialCommitment!=null && !roots[0].equals(polynomialCommitment)) throw new Error("Proof stream doesn't include required polynomial commitment");

        //Extract last codeword
        const lastCodeword = proofStream.pullBigInts(byteLength);
        const lastCodewordCommitHash = new MerkleTree(lastCodeword, byteLength).commit();

        //Check if last codeword matches lsat merkle root
        if(!roots[roots.length-1].equals(lastCodewordCommitHash)) {
            throw new Error("Last codeword doesn't match it's merkle root");
        }

        const expectedDegree = (lastCodeword.length / this.expansionFactor) - 1;
        let lastOmega = omega;
        let lastOffset = offset;
        for(let i=0;i<rounds-1;i++) {
            lastOmega = this.field.mul(lastOmega, lastOmega);
            lastOffset = this.field.mul(lastOffset, lastOffset);
        }

        //Check omega's order
        if(this.field.inv(lastOmega) !== this.field.exp(lastOmega, BigInt(lastCodeword.length-1))) throw new Error("Omega doesn't have the right order");

        const lastDomain = this.field.getPowerSeries(lastOmega, lastCodeword.length).toValues()
            .map(val => this.field.mul(lastOffset, val));

        //Interpolate poly
        const poly = Polynomial.interpolateDomain(
            lastDomain,
            lastCodeword,
            this.field
        );

        //Evaluate poly
        const evaluatedCodeword = poly.evaluateDomain(lastDomain);
        for(let i=0;i<evaluatedCodeword.length;i++) {
            if(lastCodeword[i]!==evaluatedCodeword[i]) throw new Error("Re-evaluated codeword doesn't match original");
        }

        const lastPolynomialDegree = poly.degree();
        if(poly.degree() > expectedDegree) {
            throw new Error("Last codeword doesn't correspond to a polynomial of low degree, expected: "
                +expectedDegree+", observed: "+lastPolynomialDegree);
        }

        const topCodewordPoints = Array<bigint[]>(2*this.numColinearityTests);

        //Get codeword indices
        const topLevelIndices = this.sampleIndices(proofStream.verifierFiatShamir(), this.domainLength >> 1, this.domainLength >> (rounds-1), this.numColinearityTests);

        //Run colinearity tests
        for(let i=0;i<rounds-1;i++) {

            const currentDomainLength = this.domainLength >> (i+1);

            for(let j=0;j<this.numColinearityTests;j++) {
                const computedIndex = topLevelIndices[j] % currentDomainLength;

                //Verify correct commitment
                const fA = proofStream.pullBigInt();
                const proofA = proofStream.pull();
                if(!MerkleTree.verify(roots[i], computedIndex, proofA, fA, byteLength)) throw new Error("Merkle proof verify failed for f(A)");

                const fB = proofStream.pullBigInt();
                const proofB = proofStream.pull();
                if(!MerkleTree.verify(roots[i], currentDomainLength + computedIndex, proofB, fB, byteLength)) throw new Error("Merkle proof verify failed for f(B)");

                const fC = proofStream.pullBigInt();
                const proofC = proofStream.pull();
                if(!MerkleTree.verify(roots[i+1], computedIndex, proofC, fC, byteLength)) throw new Error("Merkle proof verify failed for f(C)");

                const A = this.field.mul(offset, this.field.exp(omega, BigInt(computedIndex)));
                const B = this.field.mul(offset, this.field.exp(omega, BigInt(currentDomainLength + computedIndex)));

                if(i===0) {
                    topCodewordPoints[2*j] = [A, fA];
                    topCodewordPoints[(2*j) + 1] = [B, fB];
                }

                //Check colinearity
                if(
                    !Polynomial.testColinearity([
                        [A, fA],
                        [B, fB],
                        [alphas[i], fC]
                    ], this.field)
                ) {
                    throw new Error("Colinearity test failed, round: "+i+" test: "+j);
                }

            }

            omega = this.field.mul(omega, omega);
            offset = this.field.mul(offset, offset);

        }

        return topCodewordPoints;

    }

}