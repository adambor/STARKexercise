import {FiniteField, Vector} from "@guildofweavers/galois";
import {ProofStream} from "../fiatshamir/ProofStream";
import {bigIntToBuffer, bufferToBigInt, MerkleTree} from "../merkle/MerkleTree";
import * as crypto from "crypto";
import {Polynomial} from "../polynomial/Polynomial";
import exp from "constants";
import {MultiMerkleTree} from "../merkle/MultiMerkleTree";

export class MultiFri {

    offset: bigint;
    omega: bigint;
    domainLength: number;
    field: FiniteField;
    expansionFactor: number;
    numColinearityTests: number;
    foldingFactor: number;

    constructor(
        offset: bigint,
        omega: bigint,
        domainLength: number,
        field: FiniteField,
        expansionFactor: number,
        numColinearityTests: number,
        foldingFactor: number
    ) {
        this.offset = offset;
        this.omega = omega;
        this.domainLength = domainLength;
        this.field = field;
        this.expansionFactor = expansionFactor;
        this.numColinearityTests = numColinearityTests;
        this.foldingFactor = foldingFactor;
    }

    convertCodewordToMultiFormat(codeword: bigint[]): bigint[][] {
        const codewordHalf = codeword.length/Math.pow(2, this.foldingFactor);
        const result = Array<bigint[]>(codewordHalf);
        for(let i=0;i<codewordHalf;i++) {
            result[i] = [];
            for(let j=0;j<Math.pow(2, this.foldingFactor);j++) {
                result[i][j] = codeword[i+(codewordHalf*j)];
            }
        }
        return result;
    }

    numRounds(): number {
        let codewordLength = this.domainLength;
        let numRounds = 0;
        while(codewordLength>this.expansionFactor && 4*this.numColinearityTests<=codewordLength) {
            codewordLength = codewordLength >> this.foldingFactor;
            numRounds++;
        }
        return numRounds-1;
    }

    evaluateDomain(): bigint[] {
        return this.field.getPowerSeries(this.omega, this.domainLength).toValues().map(val => this.field.mul(val, this.offset));
    }

    prove(codeword: bigint[], proofStream: ProofStream, byteLength: number): number[] {
        if(this.domainLength!==codeword.length) throw new Error("Invalid codeword length");

        const {codewordTrees, finalCodeword} = this.commit(codeword, proofStream, byteLength);

        const initialIndices = this.sampleIndices(
            proofStream.proverFiatShamir(),
            codewordTrees[1].leafs.length*Math.pow(2, this.foldingFactor),
            finalCodeword.length,
            this.numColinearityTests
        );

        const indices = Array.from(initialIndices);

        for(let i=0; i<codewordTrees.length-1; i++) {
            const codewordHalf = codewordTrees[i].leafs.length;
            indices.forEach((val, index, arr) => {
                arr[index] = val % codewordHalf;
            });
            this.query(codewordTrees[i], codewordTrees[i+1], indices, proofStream, byteLength, i===0);
        }

        return initialIndices;
    }

    provePoly(poly: Polynomial, proofStream: ProofStream, byteLength: number): number[] {
        const {codewordTrees, finalCodeword} = this.commitPoly(poly, proofStream, byteLength);

        const initialIndices = this.sampleIndices(
            proofStream.proverFiatShamir(),
            codewordTrees[1].leafs.length*Math.pow(2, this.foldingFactor),
            finalCodeword.length,
            this.numColinearityTests
        );

        const indices = Array.from(initialIndices);

        for(let i=0; i<codewordTrees.length-1; i++) {
            const codewordHalf = codewordTrees[i].leafs.length;
            indices.forEach((val, index, arr) => {
                arr[index] = val % codewordHalf;
            });
            this.query(codewordTrees[i], codewordTrees[i+1], indices, proofStream, byteLength, i===0);
        }

        return initialIndices;
    }

    commit(codeword: bigint[], proofStream: ProofStream, byteLength: number): {
        codewordTrees: MultiMerkleTree[],
        finalCodeword: bigint[]
    } {

        const two = 2n;
        const twoInverse = this.field.inv(two);
        let offset = this.offset;
        let omega = this.omega;

        const codewordTrees: MultiMerkleTree[] = [];

        const rounds = this.numRounds();

        // console.log("Rounds: ", rounds);

        for(let i=0;i<rounds*this.foldingFactor;i++) {
            // const start = Date.now();

            // console.log("Start fri round: ", i);

            if(i % this.foldingFactor === 0) {
                const pmt = new MultiMerkleTree(this.convertCodewordToMultiFormat(codeword), byteLength);

                const root = pmt.commit();
                proofStream.push(root);
                codewordTrees.push(pmt);
            }

            // console.log("PMT committed: ", i);

            const buff = Buffer.alloc(4);
            buff.writeUintBE(i, 0, 4);
            const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                proofStream.proverFiatShamir(),
                buff
            ])).digest());

            // console.log("Round "+i+", sampled alpha:"+alpha);

            // console.log("Alpha sampled: ", alpha);

            /*
            Split and fold
            2^-1 *
            (
                (1 + a*ω^-i) * f(ω^i) +
                (1 - a*ω^-1) * f(ω^(N/2 + i))
            )`
             */

            let omegaPow = 1n;
            const codewordHalfLength = codeword.length/2;
            const newCodeword = Array<bigint>(codewordHalfLength);
            for(let j=0;j<codewordHalfLength;j++) {
                const x = this.field.mul(offset, omegaPow);
                const alphaOmega = this.field.div(alpha, x);

                omegaPow = this.field.mul(omegaPow, omega);

                // if((i===0 && (
                //     j===874 ||
                //     j===1898
                // )) || (i===1 && j===874)) {
                //     const A = x;
                //     const B = this.field.mul(x, this.field.exp(this.omega, BigInt(codewordHalfLength)));
                //     console.log("Index: "+j+" X: "+A+" f(X): "+codeword[j]);
                //     console.log("Index: "+(j+codewordHalfLength)+" X: "+B+" f(X): "+codeword[codewordHalfLength + j]);
                // }

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

            // console.log("FRI folded: ", Date.now()-start);

            codeword = newCodeword;

            omega = this.field.mul(omega, omega);
            offset = this.field.mul(offset, offset);

            // console.log("Finish fri round: ", i);
        }

        console.log("last codeword size: ", codeword.length);

        //Send last codeword
        proofStream.pushBigInts(codeword, byteLength);

        return {
            codewordTrees,
            finalCodeword: codeword
        };

    }

    commitPoly(poly: Polynomial, proofStream: ProofStream, byteLength: number): {
        codewordTrees: MultiMerkleTree[],
        finalCodeword: bigint[]
    } {

        let offset = this.offset;
        let omega = this.omega;
        let domainLength = this.domainLength;

        const codewordTrees: MultiMerkleTree[] = [];

        const rounds = this.numRounds();

        // console.log("Rounds: ", rounds);

        for(let i=0;i<rounds*this.foldingFactor;i++) {
            // const start = Date.now();

            // console.log("Start fri round: ", i);

            if(i % this.foldingFactor === 0) {
                const pmt = new MultiMerkleTree(this.convertCodewordToMultiFormat(poly.evaluateAtRootsWithOffset(this.field.getPowerSeries(omega, domainLength).toValues(), offset)), byteLength);

                const root = pmt.commit();
                proofStream.push(root);
                codewordTrees.push(pmt);
            }

            // console.log("PMT committed: ", i);

            const buff = Buffer.alloc(4);
            buff.writeUintBE(i, 0, 4);
            const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                proofStream.proverFiatShamir(),
                buff
            ])).digest());


            omega = this.field.mul(omega, omega);
            offset = this.field.mul(offset, offset);
            domainLength = domainLength/2;

            poly = poly.splitAndFold(domainLength/this.expansionFactor, alpha);

            // console.log("Finish fri round: ", i);
        }

        console.log("last codeword size: ", domainLength);

        const finalCodeword = poly.evaluateAtRootsWithOffset(this.field.getPowerSeries(omega, domainLength).toValues(), offset);
        //Send last codeword
        proofStream.pushBigInts(finalCodeword, byteLength);

        return {
            codewordTrees,
            finalCodeword
        };

    }

    query(currentCodeword: MultiMerkleTree, nextCodeword: MultiMerkleTree, cIndices: number[], proofStream: ProofStream, byteLength: number, first: boolean): void {
        const halfNextCodeword = nextCodeword.leafs.length;

        for(let i=0;i<cIndices.length;i++) {
            if(first) {
                proofStream.pushBigInts(currentCodeword.leafs[cIndices[i]], byteLength);
                proofStream.push(currentCodeword.openBuffer(cIndices[i]));
            }

            const nextIndex = cIndices[i] % halfNextCodeword;
            proofStream.pushBigInts(nextCodeword.leafs[nextIndex], byteLength);
            proofStream.push(nextCodeword.openBuffer(nextIndex));
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

    verify(proofStream: ProofStream, byteLength: number, polynomialCommitment?: Buffer): Array<[number, bigint][]> {

        let offset = this.offset;
        let omega = this.omega;

        const rounds = this.numRounds();
        const roots: Buffer[] = Array<Buffer>(rounds);
        const alphas: bigint[] = Array<bigint>(rounds*this.foldingFactor);
        for(let i=0;i<rounds*this.foldingFactor;i++) {
            if(i%this.foldingFactor===0) roots[i/this.foldingFactor] = proofStream.pull();

            const buff = Buffer.alloc(4);
            buff.writeUintBE(i, 0, 4);
            const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                proofStream.verifierFiatShamir(),
                buff
            ])).digest());
            alphas[i] = alpha;
        }

        if(polynomialCommitment!=null && !roots[0].equals(polynomialCommitment)) throw new Error("Proof stream doesn't include required polynomial commitment");

        //Extract last codeword
        const lastCodeword = proofStream.pullBigInts(byteLength);

        // const lastCodewordCommitHash = new MultiMerkleTree(convertCodewordToMultiFormat(lastCodeword), byteLength).commit();
        //
        // //Check if last codeword matches lsat merkle root
        // if(!roots[roots.length-1].equals(lastCodewordCommitHash)) {
        //     throw new Error("Last codeword doesn't match it's merkle root");
        // }

        const expectedDegree = (lastCodeword.length / this.expansionFactor) - 1;
        let lastOmega = omega;
        let lastOffset = offset;
        for(let i=0;i<rounds*this.foldingFactor;i++) {
            lastOmega = this.field.mul(lastOmega, lastOmega);
            lastOffset = this.field.mul(lastOffset, lastOffset);
        }

        //Check omega's order
        if(this.field.inv(lastOmega) !== this.field.exp(lastOmega, BigInt(lastCodeword.length-1))) throw new Error("Omega doesn't have the right order");

        const lastDomain = this.field.getPowerSeries(lastOmega, lastCodeword.length).toValues();
            //.map(val => this.field.mul(lastOffset, val));

        //Interpolate poly
        const poly = Polynomial.interpolateAtRootsWithOffset(
            lastDomain,
            lastCodeword,
            lastOffset,
            this.field
        );

        //Evaluate poly
        const evaluatedCodeword = poly.evaluateAtRootsWithOffset(lastDomain, lastOffset);
        for(let i=0;i<evaluatedCodeword.length;i++) {
            if(lastCodeword[i]!==evaluatedCodeword[i]) throw new Error("Re-evaluated codeword doesn't match original");
        }

        const lastPolynomialDegree = poly.degree();
        if(poly.degree() > expectedDegree) {
            throw new Error("Last codeword doesn't correspond to a polynomial of low degree, expected: "
                +expectedDegree+", observed: "+lastPolynomialDegree);
        }

        const topCodewordPoints = Array<[number, bigint][]>(this.numColinearityTests);

        //Get codeword indices
        //TODO: Not sure if this.domainLength >> 1 shouldn't be this.domainLength >> this.foldingFactor
        const topLevelIndices = this.sampleIndices(proofStream.verifierFiatShamir(), this.domainLength >> 1, this.domainLength >> (rounds*this.foldingFactor), this.numColinearityTests);

        const lastOpened: bigint[][] = [];

        //Run colinearity tests
        for(let i=0;i<rounds;i++) {

            const currentDomainLength = this.domainLength >> (this.foldingFactor*(i+1));

            for(let j=0;j<this.numColinearityTests;j++) {
                const computedIndex = topLevelIndices[j] % currentDomainLength;

                if(i===0) {
                    lastOpened[j] = proofStream.pullBigInts(byteLength);
                    const proofAB = proofStream.pull();
                    //Verify correct commitment
                    if(!MultiMerkleTree.verify(roots[i], computedIndex, proofAB, lastOpened[j], byteLength)) throw new Error("Merkle proof verify failed for f(A) and f(B), round: "+i);

                    //Also fill up top codeword points
                    topCodewordPoints[j] = Array<[number, bigint]>(Math.pow(2, this.foldingFactor));
                }

                let expectedFCs: bigint[] = lastOpened[j];
                for(let step=0;step<this.foldingFactor;step++) {
                    const newFCs = Array<bigint>(expectedFCs.length/2);
                    const divided = currentDomainLength;
                    // console.log("Step "+step+": divided: "+divided);
                    for(let subCollinearityIndex=0;subCollinearityIndex<expectedFCs.length/2;subCollinearityIndex++) {

                        const aIndex = subCollinearityIndex;
                        const bIndex = subCollinearityIndex + (expectedFCs.length/2);

                        const fA = expectedFCs[aIndex];
                        const fB = expectedFCs[bIndex];

                        const offsetPow = this.field.exp(offset, BigInt(Math.pow(2, step)));
                        const A = this.field.mul(offsetPow, this.field.exp(omega, BigInt(Math.pow(2, step) * (computedIndex+(aIndex*divided)))));
                        const B = this.field.mul(offsetPow, this.field.exp(omega, BigInt(Math.pow(2, step) * (computedIndex+(bIndex*divided)))));

                        if(i===0 && step===0) {
                            // console.log("Index: "+(computedIndex + (aIndex * divided))+" X: "+A+" f(X): "+fA);
                            // console.log("Index: "+(computedIndex + (bIndex * divided))+" X: "+B+" f(X): "+fB);
                            // topCodewordPoints[(Math.pow(2, this.foldingFactor) * j) + aIndex] = [computedIndex + (aIndex * divided), fA];
                            // topCodewordPoints[(Math.pow(2, this.foldingFactor) * j) + bIndex] = [computedIndex + (bIndex * divided), fB];
                            topCodewordPoints[j][aIndex] = [computedIndex + (aIndex * divided), fA];
                            topCodewordPoints[j][bIndex] = [computedIndex + (bIndex * divided), fB];
                        }

                        const alpha = alphas[(i*this.foldingFactor)+step];

                        const slope = this.field.div(
                            this.field.sub(fB, fA),
                            this.field.sub(B, A)
                        );

                        const valueAtA = this.field.mul(slope, A);
                        const slopeOffset = this.field.sub(fA, valueAtA);

                        newFCs[subCollinearityIndex] = this.field.add(this.field.mul(slope, alpha), slopeOffset);

                        // const poly = Polynomial.interpolateDomain([A, B], [fA, fB], this.field);
                        //
                        // // console.log("Round "+((i*this.foldingFactor)+step)+", sampled alpha:"+alpha);
                        // //Test collinearity;
                        // newFCs[subCollinearityIndex] = poly.evaluate(alpha);
                    }
                    expectedFCs = newFCs;
                }

                const expectedFC = expectedFCs[0];

                const nextDomainLength = currentDomainLength >> this.foldingFactor;
                let currentOpened: bigint[];
                let fC: bigint;
                if(i===rounds-1) {
                    fC = lastCodeword[computedIndex];
                } else {
                    currentOpened = proofStream.pullBigInts(byteLength);
                    const proofC = proofStream.pull();
                    if(!MultiMerkleTree.verify(roots[i+1], computedIndex % nextDomainLength, proofC, currentOpened, byteLength)) throw new Error("Merkle proof verify failed for f(C)");

                    const index = Math.floor(computedIndex/nextDomainLength);
                    fC = currentOpened[index];
                }

                //Check colinearity
                if(expectedFC!==fC) {
                    throw new Error("Colinearity test failed, round: "+i+" test: "+j+" expected: "+expectedFC+" got: "+fC);
                }

                lastOpened[j] = currentOpened;

            }

            omega = this.field.exp(omega, BigInt(Math.pow(2, this.foldingFactor)));
            offset = this.field.exp(offset, BigInt(Math.pow(2, this.foldingFactor)));

        }

        return topCodewordPoints;

    }

}