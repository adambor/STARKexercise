import {Polynomial} from "./Polynomial";
import {Fri} from "../fri/Fri";
import {MerkleTree} from "../merkle/MerkleTree";
import {ProofStream} from "../fiatshamir/ProofStream";
import * as crypto from "crypto";
import {FiniteField} from "@guildofweavers/galois";
import exp from "constants";


export class PolynomialIOP {

    static proveDegree(polynomial: Polynomial, expansionFactor: number, securityLevel: number, byteLength: number, proofStream: ProofStream): Buffer {

        const field = polynomial.field;

        const polynomialDegree= polynomial.degree();

        let provingDegree = 1;

        while(provingDegree<polynomialDegree+1) {
            provingDegree *= 2;
        }

        const evaluationDomain = expansionFactor*provingDegree;

        const omega = polynomial.field.getRootOfUnity(evaluationDomain);

        const powersOfOmega = polynomial.field.getPowerSeries(omega, evaluationDomain);

        //We need to prove that this has degree of {polynomialDegree}
        const originalCodeword = polynomial.evaluateAtRoots(powersOfOmega.toValues());
        const originalPolynomialPMT = new MerkleTree(originalCodeword, byteLength);

        proofStream.push(originalPolynomialPMT.commit());

        const entropy = proofStream.proverFiatShamir();

        const alpha = field.prng(crypto.createHash("sha256").update(Buffer.concat([
            entropy,
            Buffer.from("00", "hex")
        ])).digest());

        const beta = field.prng(crypto.createHash("sha256").update(Buffer.concat([
            entropy,
            Buffer.from("01", "hex")
        ])).digest());

        //Create a codeword for polynomial of {provingDegree}
        const friCodeword = originalCodeword.map((fX, index) => {
            const x = powersOfOmega.getValue(index);
            return field.mul(
                field.add(
                    alpha,
                    field.mul(
                        beta,
                        field.exp(x, BigInt(provingDegree-polynomialDegree-1))
                    )
                ),
                fX
            );
        });
        const friPMT = new MerkleTree(friCodeword, byteLength);

        proofStream.push(friPMT.commit());

        const entropy2 = proofStream.proverFiatShamir();

        //Open lambda leafs of both merkle trees for verifier to check
        let i = 0;
        let checks = 0;
        const openedSet = new Set<number>();
        while(checks<securityLevel) {
            i++;
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(i, 0, 6);

            const index = Number(field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    entropy2,
                    counterBuffer
                ])).digest()
            ) % BigInt(evaluationDomain));

            if(openedSet.has(index)) continue;

            proofStream.pushBigInt(originalCodeword[index], byteLength);
            proofStream.push(originalPolynomialPMT.openBuffer(index));

            proofStream.pushBigInt(friCodeword[index], byteLength);
            proofStream.push(friPMT.openBuffer(index));

            openedSet.add(index);
            checks++;
        }

        const fri = new Fri(1n, omega, evaluationDomain, field, expansionFactor, securityLevel/2);
        fri.prove(friCodeword, proofStream, byteLength);

        return originalPolynomialPMT.commit();

    }

    static proveDegrees(
        field: FiniteField,
        polynomials: (Polynomial | {
            degree: number,
            codeword: bigint[]
        })[],
        offset: bigint,
        expansionFactor: number,
        securityLevel: number,
        byteLength: number,
        proofStream: ProofStream
    ): Buffer[] {

        const start = Date.now();

        const polynomialDegrees = Array<number>(polynomials.length);
        let highestPolynomialDegree = Math.max(...polynomials.map((val, index) => {
            let degree: number;
            if(val instanceof Polynomial) {
                degree = val.degree();
            } else {
                degree = val.degree;
            }
            polynomialDegrees[index] = degree;
            return degree;
        }));

        let provingDegree = 1;

        while(provingDegree<highestPolynomialDegree+1) {
            provingDegree *= 2;
        }

        const evaluationDomain = expansionFactor*provingDegree;

        const omega = field.getRootOfUnity(evaluationDomain);

        const powersOfOmega = field.getPowerSeries(omega, evaluationDomain).toValues();

        console.log("Powers of omega calculated: ", Date.now()-start);

        //We need to prove that this has degree of {polynomialDegree}
        const originalCodewords: bigint[][] = Array<bigint[]>(polynomials.length);
        const originalPMTs: MerkleTree[] = Array<MerkleTree>(polynomials.length);

        const friCodeword = Array<bigint>(evaluationDomain);

        polynomials.forEach((poly, index) => {
            if(poly instanceof Polynomial) {
                originalCodewords[index] = poly.scale(offset).evaluateAtRoots(powersOfOmega);
            } else {
                originalCodewords[index] = poly.codeword;
            }
            originalPMTs[index] = new MerkleTree(originalCodewords[index], byteLength);

            proofStream.push(originalPMTs[index].commit());

            const entropy = proofStream.proverFiatShamir();

            const alpha = field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                Buffer.from("00", "hex")
            ])).digest());

            const beta = field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                Buffer.from("01", "hex")
            ])).digest());

            originalCodewords[index].forEach((fX, i) => {
                if(friCodeword[i]==null) friCodeword[i] = 0n;

                const x = field.mul(offset, powersOfOmega[i]);
                const addVal = field.mul(
                    field.add(
                        alpha,
                        field.mul(
                            beta,
                            field.exp(x, BigInt(provingDegree-polynomialDegrees[index]-1))
                        )
                    ),
                    fX
                );

                friCodeword[i] = field.add(friCodeword[i], addVal);
            });

        });

        console.log("Polynomials committed: ", Date.now()-start);

        const friPMT = new MerkleTree(friCodeword, byteLength);

        console.log("FRI polynomial committed: ", Date.now()-start);

        proofStream.push(friPMT.commit());

        const entropy2 = proofStream.proverFiatShamir();

        //Open lambda leafs of all merkle trees for verifier to check
        let i = 0;
        let checks = 0;
        const openedSet = new Set<number>();
        while(checks<securityLevel) {
            i++;
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(i, 0, 6);

            const index = Number(field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    entropy2,
                    counterBuffer
                ])).digest()
            ) % BigInt(evaluationDomain));

            if(openedSet.has(index)) continue;

            originalPMTs.forEach((pmt, polynomialIndex) => {
                proofStream.pushBigInt(originalCodewords[polynomialIndex][index], byteLength);
                proofStream.push(pmt.openBuffer(index));
            });

            proofStream.pushBigInt(friCodeword[index], byteLength);
            proofStream.push(friPMT.openBuffer(index));

            openedSet.add(index);
            checks++;
        }

        console.log("Random checks proven: ", Date.now()-start);

        const fri = new Fri(offset, omega, evaluationDomain, field, expansionFactor, securityLevel/2);
        fri.prove(friCodeword, proofStream, byteLength);

        return originalPMTs.map(pmt => pmt.commit());

    }

    static verifyDegree(field: FiniteField, polynomialCommitment: Buffer, polynomialDegree: number, proofStream: ProofStream, expansionFactor: number, securityLevel: number, byteLength: number): void {

        let provingDegree = 1;

        while(provingDegree<polynomialDegree+1) {
            provingDegree *= 2;
        }

        const evaluationDomain = expansionFactor*provingDegree;

        const omega = field.getRootOfUnity(evaluationDomain);

        const powersOfOmega = field.getPowerSeries(omega, evaluationDomain);

        //Read commitment to original polynomial;
        const streamPolynomialCommitment = proofStream.pull();
        if(!streamPolynomialCommitment.equals(polynomialCommitment)) throw new Error("Stream doesn't contain commitment to this polynomial!");

        const entropy = proofStream.verifierFiatShamir();

        const alpha = field.prng(crypto.createHash("sha256").update(Buffer.concat([
            entropy,
            Buffer.from("00", "hex")
        ])).digest());

        const beta = field.prng(crypto.createHash("sha256").update(Buffer.concat([
            entropy,
            Buffer.from("01", "hex")
        ])).digest());

        //Read friCommitment
        const friPolynomialCommitment = proofStream.pull();

        const entropy2 = proofStream.verifierFiatShamir();

        //Verify lambda checks between commitments

        let i = 0;
        let checks = 0;
        const openedSet = new Set<number>();
        while(checks<securityLevel) {
            i++;
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(i, 0, 6);

            const index = Number(field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    entropy2,
                    counterBuffer
                ])).digest()
            ) % BigInt(evaluationDomain));

            if(openedSet.has(index)) continue;

            const x = field.exp(omega, BigInt(index));

            const fX = proofStream.pullBigInt();
            const fXproof = proofStream.pull();
            if(!MerkleTree.verify(polynomialCommitment, index, fXproof, fX, byteLength)) throw new Error("fX inclusion proof invalid");

            const expected = field.mul(
                field.add(
                    alpha,
                    field.mul(
                        beta,
                        field.exp(x, BigInt(provingDegree-polynomialDegree-1))
                    )
                ),
                fX
            );

            const gX = proofStream.pullBigInt();
            const gXproof = proofStream.pull();
            if(!MerkleTree.verify(friPolynomialCommitment, index, gXproof, gX, byteLength)) throw new Error("gX inclusion proof invalid");

            if(expected!==gX) throw new Error("Invalid FRI codeword g(x)!==expected");

            openedSet.add(index);
            checks++;
        }

        const fri = new Fri(1n, omega, evaluationDomain, field, expansionFactor, securityLevel/2);
        fri.verify(proofStream, byteLength, friPolynomialCommitment);

    }

    static verifyDegrees(
        field: FiniteField,
        polynomials: {
            commitment: Buffer,
            degree: number
        }[],
        offset: bigint,
        expansionFactor: number,
        securityLevel: number,
        byteLength: number,
        proofStream: ProofStream
    ): void {

        const polynomialDegrees = Array<number>(polynomials.length);
        let highestPolynomialDegree = Math.max(...polynomials.map((val, index) => {
            polynomialDegrees[index] = val.degree;
            return val.degree;
        }));

        let provingDegree = 1;

        while(provingDegree<highestPolynomialDegree+1) {
            provingDegree *= 2;
        }

        const evaluationDomain = expansionFactor*provingDegree;

        const omega = field.getRootOfUnity(evaluationDomain);

        const powersOfOmega = field.getPowerSeries(omega, evaluationDomain).toValues();

        const alphas = Array<bigint>(polynomials.length);
        const betas = Array<bigint>(polynomials.length);

        polynomials.forEach((poly, index) => {
            const polyCommitment = proofStream.pull();
            if(!polyCommitment.equals(poly.commitment)) throw new Error("Stream doesn't contain commitment to this polynomial! Index: "+index);

            const entropy = proofStream.verifierFiatShamir();

            const alpha = field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                Buffer.from("00", "hex")
            ])).digest());

            const beta = field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                Buffer.from("01", "hex")
            ])).digest());

            alphas[index] = alpha;
            betas[index] = beta;

        });

        const friPolynomialCommitment = proofStream.pull();

        const entropy2 = proofStream.verifierFiatShamir();

        //Open lambda leafs of all merkle trees for verifier to check
        let i = 0;
        let checks = 0;
        const openedSet = new Set<number>();
        while(checks<securityLevel) {
            i++;
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(i, 0, 6);

            const index = Number(field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    entropy2,
                    counterBuffer
                ])).digest()
            ) % BigInt(evaluationDomain));

            if(openedSet.has(index)) continue;

            let friAccumulator = 0n;

            polynomials.forEach((poly, polynomialIndex) => {

                const fX = proofStream.pullBigInt();
                const fXproof = proofStream.pull();
                if(!MerkleTree.verify(poly.commitment, index, fXproof, fX, byteLength)) throw new Error("fX inclusion proof invalid");

                const x = field.mul(offset, powersOfOmega[index]);
                const addVal = field.mul(
                    field.add(
                        alphas[polynomialIndex],
                        field.mul(
                            betas[polynomialIndex],
                            field.exp(x, BigInt(provingDegree-polynomialDegrees[polynomialIndex]-1))
                        )
                    ),
                    fX
                );

                friAccumulator = field.add(friAccumulator, addVal);
            });

            const gX = proofStream.pullBigInt();
            const gXproof = proofStream.pull();
            if(!MerkleTree.verify(friPolynomialCommitment, index, gXproof, gX, byteLength)) throw new Error("gX inclusion proof invalid");

            if(friAccumulator!==gX) throw new Error("Invalid FRI codeword g(x)!==expected");

            openedSet.add(index);
            checks++;
        }

        const fri = new Fri(offset, omega, evaluationDomain, field, expansionFactor, securityLevel/2);
        fri.verify(proofStream, byteLength, friPolynomialCommitment);

    }

    static proveEvaluation(
        polynomial: Polynomial,
        evaluationPoint: bigint,
        offset: bigint,
        expansionFactor: number,
        securityLevel: number,
        byteLength: number,
        proofStream: ProofStream
    ): Buffer {
        const start = Date.now();

        const field = polynomial.field;

        const fZ = polynomial.evaluate(evaluationPoint);
        const z = evaluationPoint;

        const degree = polynomial.degree();
        let provingDegree = 1;
        while(provingDegree<degree+1) {
            provingDegree *= 2;
        }
        const evaluationDomain = expansionFactor*provingDegree;

        const omega = field.getRootOfUnity(evaluationDomain);
        const powersOfOmega = field.getPowerSeries(omega, evaluationDomain);

        console.log("Power series calculated: ", Date.now()-start);

        const polynomialCodeword = polynomial.scale(offset).evaluateAtRoots(powersOfOmega.toValues());
        const polynomialPMT = new MerkleTree(polynomialCodeword, byteLength);

        console.log("Polynomial evaluated: ", Date.now()-start);

        const quotientCodeword = polynomialCodeword.map((val, index) => {
            const dividend = field.sub(val, fZ);
            const divisor = field.sub(field.mul(offset, powersOfOmega.getValue(index)), z);
            if(divisor===0n) throw new Error("Cannot divide by 0!");
            return field.div(
                dividend,
                divisor
            );
        });
        const quotientPMT = new MerkleTree(quotientCodeword, byteLength);

        console.log("Quotient codeword derived: ", Date.now()-start);

        proofStream.push(polynomialPMT.commit());
        proofStream.push(quotientPMT.commit());

        const entropy = proofStream.proverFiatShamir();

        //Open lambda leafs of all merkle trees for verifier to check
        let i = 0;
        let checks = 0;
        const openedSet = new Set<number>();
        while(checks<securityLevel) {
            i++;
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(i, 0, 6);

            const index = Number(field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    entropy,
                    counterBuffer
                ])).digest()
            ) % BigInt(evaluationDomain));

            if (openedSet.has(index)) continue;

            proofStream.pushBigInt(polynomialCodeword[index], byteLength);
            proofStream.push(polynomialPMT.openBuffer(index));

            proofStream.pushBigInt(quotientCodeword[index], byteLength);
            proofStream.push(quotientPMT.openBuffer(index));

            openedSet.add(index);
            checks++;
        }

        console.log("Random check proofs computed: ", Date.now()-start);

        PolynomialIOP.proveDegrees(field, [
            {
                codeword: polynomialCodeword,
                degree
            },
            {
                codeword: quotientCodeword,
                degree: degree-1
            }
        ], offset, expansionFactor, securityLevel, byteLength, proofStream);

        console.log("FRI proven: ", Date.now()-start);

        return polynomialPMT.commit();

    }

    static verifyEvaluation(
        field: FiniteField,
        polynomialCommitment: Buffer,
        degree: number,
        evaluationPoint: bigint,
        evaluationValue: bigint,
        offset: bigint,
        expansionFactor: number,
        securityLevel: number,
        byteLength: number,
        proofStream: ProofStream
    ) {

        const fZ = evaluationValue;
        const z = evaluationPoint;

        let provingDegree = 1;
        while(provingDegree<degree+1) {
            provingDegree *= 2;
        }
        const evaluationDomain = expansionFactor*provingDegree;

        const omega = field.getRootOfUnity(evaluationDomain);
        const powersOfOmega = field.getPowerSeries(omega, evaluationDomain);

        if(!proofStream.pull().equals(polynomialCommitment)) throw new Error("Invalid polynomial commitment in proof stream");
        const quotientCommitment = proofStream.pull();

        const entropy = proofStream.verifierFiatShamir();

        //Open lambda leafs of all merkle trees for verifier to check
        let i = 0;
        let checks = 0;
        const openedSet = new Set<number>();
        while(checks<securityLevel) {
            i++;
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(i, 0, 6);

            const index = Number(field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    entropy,
                    counterBuffer
                ])).digest()
            ) % BigInt(evaluationDomain));

            if (openedSet.has(index)) continue;

            const fX = proofStream.pullBigInt();
            const fXproof = proofStream.pull();
            if(!MerkleTree.verify(polynomialCommitment, index, fXproof, fX, byteLength)) throw new Error("fX inclusion proof invalid");

            const quotient = proofStream.pullBigInt();
            const quotientProof = proofStream.pull();
            if(!MerkleTree.verify(quotientCommitment, index, quotientProof, quotient, byteLength)) throw new Error("quotient inclusion proof invalid");

            const expectedValue = field.div(
                field.sub(fX, fZ),
                field.sub(field.mul(offset, powersOfOmega.getValue(index)), z)
            );

            if(expectedValue!==quotient) throw new Error("quotient doesn't have expected value");

            openedSet.add(index);
            checks++;
        }

        PolynomialIOP.verifyDegrees(field, [
            {
                commitment: polynomialCommitment,
                degree: degree
            },
            {
                commitment: quotientCommitment,
                degree: degree-1
            }
        ], offset, expansionFactor, securityLevel, byteLength, proofStream);

    }

}