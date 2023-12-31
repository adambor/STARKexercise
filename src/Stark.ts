import {FiniteField} from "@guildofweavers/galois";
import {MultiPolynomial} from "./polynomial/MultiPolynomial";
import {Polynomial} from "./polynomial/Polynomial";
import {ProofStream} from "./fiatshamir/ProofStream";
import {MerkleTree} from "./merkle/MerkleTree";
import * as crypto from "crypto";
import {Fri} from "./fri/Fri";
import {MultiMerkleTree} from "./merkle/MultiMerkleTree";
import {MultiFri} from "./fri/MultiFri";

export type BoundaryConditions = Map<number, {
    cycle: number,
    value: bigint
}[]>;

export class Stark {

    field: FiniteField;
    byteLength: number;

    securityLevel: number;
    expansionFactor: number;
    numColinearityChecks: number;
    numRegisters: number;
    numCycles: number;
    transitionConstraintsDegree: number;

    omicron: bigint;
    omicronDomain: bigint[];

    omega: bigint;
    omegaDomain: bigint[];

    friOffset: bigint;
    foldingFactor: number;

    constructor(
        field: FiniteField,
        byteLength: number,
        expansionFactor: number,
        securityLevel: number,
        numRegisters: number,
        numCycles: number,
        transitionConstraintsDegree: number,
        friOffset: bigint,
        foldingFactor?: number
    ) {

        this.field = field;
        this.byteLength = byteLength;
        this.securityLevel = securityLevel;
        this.expansionFactor = expansionFactor;
        this.numColinearityChecks = Math.ceil(securityLevel/Math.log2(expansionFactor));
        this.numRegisters = numRegisters;
        this.numCycles = numCycles;
        this.transitionConstraintsDegree = transitionConstraintsDegree;

        let omicronDomainLength = 1;
        while(omicronDomainLength < this.numCycles*transitionConstraintsDegree) {
            omicronDomainLength *= 2;
        }

        this.omicron = this.field.getRootOfUnity(omicronDomainLength);
        this.omicronDomain = this.field.getPowerSeries(this.omicron, omicronDomainLength).toValues();

        this.omega = this.field.getRootOfUnity(omicronDomainLength*expansionFactor);
        this.omegaDomain = this.field.getPowerSeries(this.omega, omicronDomainLength*expansionFactor).toValues();

        this.friOffset = friOffset;
        this.foldingFactor = foldingFactor || 1;

    }

    sampleNumbers(seed: Buffer, maxSize: number, count: number): number[] {

        const computedIndices = [];
        let counter = 0;

        while(computedIndices.length<count) {
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(counter, 0, 6);
            const index = Number(this.field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    seed,
                    counterBuffer
                ])).digest()
            ) % BigInt(maxSize));

            computedIndices.push(index);

            counter++;
        }

        return computedIndices;

    }

    sampleIndices(seed: Buffer, maxSize: number, alreadyUsed: Set<number>, count: number): number[] {

        const computedIndices = [];
        let counter = 0;

        while(computedIndices.length<count) {
            const counterBuffer = Buffer.alloc(6);
            counterBuffer.writeUintBE(counter, 0, 6);
            const index = Number(this.field.prng(
                crypto.createHash("sha256").update(Buffer.concat([
                    seed,
                    counterBuffer
                ])).digest()
            ) % BigInt(maxSize));

            if(!alreadyUsed.has(index)) {
                alreadyUsed.add(index);
                computedIndices.push(index);
            }

            counter++;
        }

        return computedIndices;

    }

    transitionDegreeBounds(constraints: MultiPolynomial[]): number[] {

        const traceDegrees = this.numCycles-1;

        return constraints.map((constraint) => {
            let maxPower = 0;
            for(let powers of constraint.coefficients.keys()) {
                let sum = 0;
                powers.forEach((val, index) => {
                    sum += Number(val) * (index===0 ? 1 : traceDegrees);
                });
                maxPower = Math.max(maxPower, sum);
            }
            return maxPower;
        });

    }

    transitionQuotientDegreeBounds(transitionDegreeBounds: number[]): number[] {
        return transitionDegreeBounds.map(d => d - (this.numCycles - 1));
    }

    maxDegreeQuotientDegree(transitionQuotientDegreeBounds: number[]): number {
        return Math.max(...transitionQuotientDegreeBounds);
    }

    transitionZerofier() {
        return Polynomial.fastZerofier(this.omicronDomain.slice(0, this.numCycles-1), this.field);
    }

    boundaryZerofiers(points: BoundaryConditions): Polynomial[] {
        const boundaryZerofiers = Array<Polynomial>(this.numRegisters);
        for(let i=0;i<this.numRegisters;i++) {
            const registerPoints = points.get(i);
            if(registerPoints==null) {
                boundaryZerofiers[i] = null;
                continue;
            }
            boundaryZerofiers[i] = Polynomial.fastZerofier(registerPoints.map(val => this.omicronDomain[val.cycle]), this.field);
        }
        return boundaryZerofiers;
    }

    boundaryInterpolants(points: BoundaryConditions): Polynomial[] {
        const boundaryInterpolants = Array<Polynomial>(this.numRegisters);
        for(let i=0;i<this.numRegisters;i++) {
            const registerPoints = points.get(i);
            if(registerPoints==null) {
                boundaryInterpolants[i] = null;
                continue;
            }
            boundaryInterpolants[i] = Polynomial.interpolateDomain(
                registerPoints.map(val => this.omicronDomain[val.cycle]),
                registerPoints.map(val => val.value),
                this.field
            );
        }
        return boundaryInterpolants;
    }

    boundaryQuotientDegreeBounds(boundaryZerofiers: Polynomial[]): number[] {
        return boundaryZerofiers.map(zerofier => zerofier==null ? null : this.numCycles-1 - zerofier.degree());
    }

    prove(trace: bigint[][], transitionConstraints: MultiPolynomial[], boundaryConditions: BoundaryConditions, proofStream: ProofStream, runChecks?: boolean) {

        const executionDomain = this.omicronDomain.slice(0, this.numCycles);

        //Interpolate trace polys
        console.time("STARK.prove: Trace interpolation");
        const zerofierCache = {};
        const tracePolynomials: Polynomial[] = trace.map(values => {
            const times = [0,0,0,0,0];
            const result = Polynomial.fastFFTInterpolate(this.omicronDomain, values, this.field, null, times, zerofierCache);
            console.log("Times: ", times);
            return result;
        });
        const tracePolynomialsPlus1: Polynomial[] = tracePolynomials.map(poly => poly.scale(this.omicron));
        console.timeEnd("STARK.prove: Trace interpolation");

        console.time("STARK.prove: Boundary polys");
        const boundaryInterpolants = this.boundaryInterpolants(boundaryConditions);
        const boundaryZerofiers = this.boundaryZerofiers(boundaryConditions);
        console.timeEnd("STARK.prove: Boundary polys");

        //Boundary zerofier and interpolants codewords
        // console.time("STARK.prove: Boundary codewords");
        // const boundaryInterpolantsCodewords: bigint[][] = boundaryInterpolants.map(poly => poly==null ? null : poly.evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset));
        // const boundaryZerofiersCodewords: bigint[][] = boundaryZerofiers.map(poly => poly==null ? null : poly.evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset));
        // console.timeEnd("STARK.prove: Boundary codewords");

        //Obtain quotient codewords
        console.time("STARK.prove: Boundary quotient codewords");
        const boundaryQuotientPolys: Polynomial[] = tracePolynomials.map((tracePolynomial, registerIndex) => {
            // const boundaryInterpolantCodeword = boundaryInterpolantsCodewords[registerIndex];
            // const boundaryZerofiersCodeword = boundaryZerofiersCodewords[registerIndex];

            if (boundaryInterpolants[registerIndex] == null) return null;

            /**
             * f - trace
             * B - boundary interpolant
             * Zb - boundary zerofier
             *
             * (f(x)-B(x)) / Zb(x)
             */
            return tracePolynomial.sub(boundaryInterpolants[registerIndex]).divide(boundaryZerofiers[registerIndex]);

            // return codeword.map((value, index) => {
            //     return this.field.div(
            //         this.field.sub(value, boundaryInterpolantCodeword[index]),
            //         boundaryZerofiersCodeword[index]
            //     )
            // });
        });
        console.timeEnd("STARK.prove: Boundary quotient codewords");

        if(runChecks) {
            const _boundaryQuotientPolyDegrees = boundaryQuotientPolys.map(poly => poly==null ? null : poly.degree());
            console.log("Boundary quotient poly degrees: ", _boundaryQuotientPolyDegrees);
            console.log("Expected boundary quotient poly degrees: ", this.boundaryQuotientDegreeBounds(boundaryZerofiers));
            const reconstructedTraces = boundaryQuotientPolys.map((quotientPoly, index) => quotientPoly==null ? null : quotientPoly.fastMul(boundaryZerofiers[index]).add(boundaryInterpolants[index]));
            console.log("Reconstructed traces match: ", reconstructedTraces.map((reconstructedTrace, index) => reconstructedTrace==null ? null : reconstructedTrace.equals(tracePolynomials[index])));
        }

        //Map boundary quotient codewords (use raw traces for registries without boundary constraints) to PMTs
        console.time("STARK.prove: Commit boundary quotient/trace");
        const combinedCodewords: bigint[][] = Array<bigint[]>(this.omegaDomain.length);
        boundaryQuotientPolys.forEach((poly, polyIndex) => {
            if(poly==null) poly = tracePolynomials[polyIndex];
            const codeword = poly.evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset)

            codeword.forEach((e, index) => {
                if(combinedCodewords[index]==null) combinedCodewords[index] = Array<bigint>(boundaryQuotientPolys.length);
                combinedCodewords[index][polyIndex] = e;
            })
        });

        const combinedPMT = new MultiMerkleTree(combinedCodewords, this.byteLength);

        //Commit boundary quotients & possibly traces
        proofStream.push(combinedPMT.commit());
        console.timeEnd("STARK.prove: Commit boundary quotient/trace");

        //Transition zerofier Zt - value of 0 on point 0...this.numCycles-1
        console.time("STARK.prove: Transition zerofier");
        const transitionZerofier = this.transitionZerofier();
        // const transitionZerofierCodewords = transitionZerofier.evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset);
        console.timeEnd("STARK.prove: Transition zerofier");

        //Evaluate transition codewords - evaluation of multivariant polynomials Mt(x, P1i, P2i, ..., P1i+1, P2i+1, ...)
        // console.time("STARK.prove: Transition codewords");
        // const transitionCodewords: bigint[][] = transitionConstraints.map(transitionPolynomial => {
        //     return this.omegaDomain.map((omegaPower, i) => {
        //         const x = this.field.mul(omegaPower, this.friOffset);
        //         return transitionPolynomial.evaluate(
        //             [x].concat(
        //                 traceCodewords.map(codeword => codeword[i]),
        //                 traceCodewordsPlus1.map(codeword => codeword[i])
        //             )
        //         );
        //     });
        // });
        // console.timeEnd("STARK.prove: Transition codewords");

        /**
         * Mt - transition multivariant polynomial
         * Zt - transition zerofier
         *
         * Mt(x, P1i, P2i, ..., P1i+1, P2i+1, ...) / Zb(x)
         */
        console.time("STARK.prove: Transition quotient codewords");
        // const transitionQuotientCodewords: bigint[][] = transitionCodewords.map(codeword => {
        //     return codeword.map((value, i) => this.field.div(value, transitionZerofierCodewords[i]));
        // });
        const xOnlyPolynomial = new Polynomial(this.field.newVectorFrom([0n, 1n]), this.field);
        const transitionPolys = transitionConstraints.map(transitionPolynomial => {
            return transitionPolynomial.evaluateSymbolic([xOnlyPolynomial].concat(
                tracePolynomials,
                tracePolynomialsPlus1
            ));
        });
        const transitionQuotientPolys: Polynomial[] = transitionPolys.map(transitionPolynomial => transitionPolynomial.divide(transitionZerofier));
        // const transitionQuotientCodewords: bigint[][] = transitionQuotientPolys.map(transitionQuotientPolynomial => {
        //     return transitionQuotientPolynomial.evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset);
        // });
        console.timeEnd("STARK.prove: Transition quotient codewords");

        const entropy = proofStream.proverFiatShamir();

        //Get degree bounds for respective transition quotients, these depend on the degree of the transition constraints
        console.time("STARK.prove: Transition quotient degree bounds");
        const transitionQuotientDegreeBounds = this.transitionQuotientDegreeBounds(this.transitionDegreeBounds(transitionConstraints));
        console.timeEnd("STARK.prove: Transition quotient degree bounds");

        if(runChecks) {
            //const transitionQuotientPolys = transitionQuotientCodewords.map(codeword => codeword==null ? null : Polynomial.interpolateDomain(this.omegaDomain.map(omegaPower => this.field.mul(omegaPower, this.friOffset)), codeword, this.field))
            const transitionQuotientPolyDegrees = transitionQuotientPolys.map(poly => poly.degree());
            console.log("Transition quotient poly degrees: ", transitionQuotientPolyDegrees);
            console.log("Expected transition quotient poly degrees: ", transitionQuotientDegreeBounds);
            const reconstructedTransitionPolys = transitionQuotientPolys.map(quotientPoly => quotientPoly.fastMul(transitionZerofier));
            console.log("Reconstructed transition polys match: ", reconstructedTransitionPolys.map((reconstructedPoly, index) => reconstructedPoly.equals(transitionPolys[index])));
        }

        //Construct FRI codeword of random weighted combinations of polys to be proven.
        //const friCodeword = Array<bigint>(this.omicronDomain.length);
        let polynomialAccumulator = new Polynomial(this.field.newVectorFrom([0n]), this.field);

        //Transition quotients
        console.time("STARK.prove: Random combination - transition quotients");
        // transitionQuotientCodewords.forEach((codeword, index) => {
        //
        //     const buff = Buffer.alloc(6);
        //     buff.writeUIntBE(index, 0, 6);
        //
        //     const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
        //         entropy,
        //         buff,
        //         Buffer.from("00", "hex")
        //     ])).digest());
        //
        //     const beta = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
        //         entropy,
        //         buff,
        //         Buffer.from("01", "hex")
        //     ])).digest());
        //
        //     codeword.forEach((fX, i) => {
        //         if(friCodeword[i]==null) friCodeword[i] = 0n;
        //
        //         const x = this.field.mul(this.friOffset, this.omegaDomain[i]);
        //         const addVal = this.field.mul(
        //             this.field.add(
        //                 alpha,
        //                 this.field.mul(
        //                     beta,
        //                     this.field.exp(x, BigInt(this.omicronDomain.length-transitionQuotientDegreeBounds[index]-1))
        //                 )
        //             ),
        //             fX
        //         );
        //
        //         friCodeword[i] = this.field.add(friCodeword[i], addVal);
        //     });
        //
        // });
        transitionQuotientPolys.forEach((quotientPolynomial, index) => {

            const buff = Buffer.alloc(6);
            buff.writeUIntBE(index, 0, 6);

            const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                buff,
                Buffer.from("00", "hex")
            ])).digest());

            const beta = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                buff,
                Buffer.from("01", "hex")
            ])).digest());

            const xPower = this.omicronDomain.length-transitionQuotientDegreeBounds[index]-1;
            const multiplicantCoefficients = [];
            multiplicantCoefficients[xPower] = beta;
            multiplicantCoefficients.fill(0n, 0, xPower);
            multiplicantCoefficients[0] = alpha;

            const resultPolynomial = quotientPolynomial.fastMul(new Polynomial(this.field.newVectorFrom(multiplicantCoefficients), this.field));

            polynomialAccumulator = polynomialAccumulator.add(resultPolynomial);

            // codeword.forEach((fX, i) => {
            //     if(friCodeword[i]==null) friCodeword[i] = 0n;
            //
            //     const x = this.field.mul(this.friOffset, this.omegaDomain[i]);
            //     const addVal = this.field.mul(
            //         this.field.add(
            //             alpha,
            //             this.field.mul(
            //                 beta,
            //                 this.field.exp(x, BigInt(this.omicronDomain.length-transitionQuotientDegreeBounds[index]-1))
            //             )
            //         ),
            //         fX
            //     );
            //
            //     friCodeword[i] = this.field.add(friCodeword[i], addVal);
            // });

        });
        console.timeEnd("STARK.prove: Random combination - transition quotients");

        let boundaryQuotientDegreeBounds = this.boundaryQuotientDegreeBounds(boundaryZerofiers);

        //Boundary quotients
        console.time("STARK.prove: Random combination - boundary quotients / traces");
        // boundaryQuotientCodewords.forEach((codeword, index) => {
        //
        //     let degreeBounds = boundaryQuotientDegreeBounds[index];
        //     if(codeword==null) {
        //         codeword = traceCodewords[index];
        //         degreeBounds = this.numCycles-1;
        //     }
        //
        //     const buff = Buffer.alloc(6);
        //     buff.writeUIntBE(index, 0, 6);
        //
        //     const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
        //         entropy,
        //         buff,
        //         Buffer.from("02", "hex")
        //     ])).digest());
        //
        //     const beta = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
        //         entropy,
        //         buff,
        //         Buffer.from("03", "hex")
        //     ])).digest());
        //
        //     codeword.forEach((fX, i) => {
        //         if(friCodeword[i]==null) friCodeword[i] = 0n;
        //
        //         const x = this.field.mul(this.friOffset, this.omegaDomain[i]);
        //         const addVal = this.field.mul(
        //             this.field.add(
        //                 alpha,
        //                 this.field.mul(
        //                     beta,
        //                     this.field.exp(x, BigInt(this.omicronDomain.length-degreeBounds-1))
        //                 )
        //             ),
        //             fX
        //         );
        //
        //         friCodeword[i] = this.field.add(friCodeword[i], addVal);
        //     });
        //
        // });
        boundaryQuotientPolys.forEach((boundaryQuotient, index) => {

            let degreeBounds = boundaryQuotientDegreeBounds[index];
            if(boundaryQuotient==null) {
                boundaryQuotient = tracePolynomials[index];
                degreeBounds = this.numCycles-1;
            }

            const buff = Buffer.alloc(6);
            buff.writeUIntBE(index, 0, 6);

            const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                buff,
                Buffer.from("02", "hex")
            ])).digest());

            const beta = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                buff,
                Buffer.from("03", "hex")
            ])).digest());


            const xPower = this.omicronDomain.length-degreeBounds-1;
            const multiplicantCoefficients = [];
            multiplicantCoefficients[xPower] = beta;
            multiplicantCoefficients.fill(0n, 0, xPower);
            multiplicantCoefficients[0] = alpha;

            const resultPolynomial = boundaryQuotient.fastMul(new Polynomial(this.field.newVectorFrom(multiplicantCoefficients), this.field));

            polynomialAccumulator = polynomialAccumulator.add(resultPolynomial);

            // codeword.forEach((fX, i) => {
            //     if(friCodeword[i]==null) friCodeword[i] = 0n;
            //
            //     const x = this.field.mul(this.friOffset, this.omegaDomain[i]);
            //     const addVal = this.field.mul(
            //         this.field.add(
            //             alpha,
            //             this.field.mul(
            //                 beta,
            //                 this.field.exp(x, BigInt(this.omicronDomain.length-degreeBounds-1))
            //             )
            //         ),
            //         fX
            //     );
            //
            //     friCodeword[i] = this.field.add(friCodeword[i], addVal);
            // });

        });
        console.timeEnd("STARK.prove: Random combination - boundary quotients / traces");

        console.time("STARK.prove: FRI");
        const fri = new MultiFri(this.friOffset, this.omega, this.omegaDomain.length, this.field, this.expansionFactor, this.numColinearityChecks, this.foldingFactor);
        const {initialIndices, codewordTrees} = fri.provePoly(polynomialAccumulator, proofStream, this.byteLength);
        console.timeEnd("STARK.prove: FRI");

        //console.log("Fri points: ", sampledPoints);

        console.time("STARK.prove: FRI Point opening");
        const omegaDomainDividedByFoldingFactor = this.omegaDomain.length/Math.pow(2, this.foldingFactor);

        const requiredAdditionalPoints = this.securityLevel-this.numColinearityChecks;
        const seed = proofStream.proverFiatShamir();
        const additionalIndices = this.sampleIndices(
            seed,
            omegaDomainDividedByFoldingFactor,
            new Set(initialIndices),
            requiredAdditionalPoints
        );

        const rootFRICodewordPMT = codewordTrees[0];
        for(let i=0;i<requiredAdditionalPoints;i++) {
            const point = additionalIndices[i];
            //Open the specific point
            proofStream.pushBigInts(rootFRICodewordPMT.leafs[point], this.byteLength);
            proofStream.push(rootFRICodewordPMT.openBuffer(point));
        }
        console.timeEnd("STARK.prove: FRI Point opening");

        //Open up leaves on the boundary quotients/trace polys
        console.time("STARK.prove: Point opening");
        const pointOffsetSelectors = this.sampleNumbers(proofStream.proverFiatShamir(), Math.pow(2, this.foldingFactor), this.securityLevel);

        for(let i=0;i<this.securityLevel;i++) {
            let point: number;
            if(i<this.numColinearityChecks) {
                //Points are already opened in FRI
                point = initialIndices[i];
            } else {
                //Belongs to additional opened indices
                point = additionalIndices[i-this.numColinearityChecks];
            }

            // console.log("Point["+i+"]: ", point);

            const pointWithOffset = point + (pointOffsetSelectors[i] * omegaDomainDividedByFoldingFactor);

            // console.log("Point with offset["+i+"]: ", pointWithOffset);

            proofStream.pushBigInts(combinedPMT.leafs[pointWithOffset], this.byteLength);
            proofStream.push(combinedPMT.openBuffer(pointWithOffset));

            const pointWithOffsetPlus1 = (pointWithOffset + this.expansionFactor) % this.omegaDomain.length;

            proofStream.pushBigInts(combinedPMT.leafs[pointWithOffsetPlus1], this.byteLength);
            proofStream.push(combinedPMT.openBuffer(pointWithOffsetPlus1));
        }
        // boundaryQuotientAndTracePMTs.forEach(codeword => {
        //     sampledPoints.forEach(i => {
        //         {
        //             proofStream.pushBigInt(codeword.leafs[i], this.byteLength);
        //             proofStream.push(codeword.openBuffer(i));
        //
        //             const secondIndex = (i + this.expansionFactor) % this.omegaDomain.length;
        //             proofStream.pushBigInt(codeword.leafs[secondIndex], this.byteLength);
        //             proofStream.push(codeword.openBuffer(secondIndex));
        //         }
        //
        //         i = i + this.omegaDomain.length/2;
        //
        //         {
        //             proofStream.pushBigInt(codeword.leafs[i], this.byteLength);
        //             proofStream.push(codeword.openBuffer(i));
        //
        //             const secondIndex = (i + this.expansionFactor) % this.omegaDomain.length;
        //             proofStream.pushBigInt(codeword.leafs[secondIndex], this.byteLength);
        //             proofStream.push(codeword.openBuffer(secondIndex));
        //         }
        //     });
        // });
        console.timeEnd("STARK.prove: Point opening");

        // const point = sampledPoints[0];
        // console.log("Traces at "+point, traceCodewords.map(val => val[point]));
        // console.log("Traces+1 at "+point, traceCodewordsPlus1.map(val => val[point]));
        // console.log("Constraint polynomials at "+point, transitionCodewords.map(val => val[point]));
        // console.log("Transition quotients at "+point, transitionQuotientCodewords.map(val => val[point]));
        // console.log("Boundary quotients at "+point, boundaryQuotientCodewords.map(val => val[point]));

    }

    verify(proofStream: ProofStream, transitionConstraints: MultiPolynomial[], boundaryConditions: BoundaryConditions) {

        /**
         * Proof:
         *  - boundaryQuotientAndTracePMTs roots
         *  + entropy for proving polynomial degree
         *  - FRI
         *  - boundaryQuotientAndTracePMTs opening at points sampled from first round of FRI
         *      - i
         *      - (i + this.expansionFactor) % this.omegaDomain.length
         */

        const boundaryQuotientAndTraceRoot = proofStream.pull();

        //console.log("boundaryQuotientAndTraceRoots", boundaryQuotientAndTraceRoots);

        const entropy = proofStream.verifierFiatShamir();

        console.time("STARK.verify: FRI");
        //Run FRI
        const fri = new MultiFri(this.friOffset, this.omega, this.omegaDomain.length, this.field, this.expansionFactor, this.numColinearityChecks, this.foldingFactor);
        let {points: expandedFriPoints, merkleRoots: friMerkleRoots} = fri.verify(proofStream, this.byteLength);
        console.timeEnd("STARK.verify: FRI");

        const topFRIMerkleRoot = friMerkleRoots[0];

        console.time("STARK.verify: Load additional FRI poly points");
        const omegaDomainDividedByFoldingFactor = this.omegaDomain.length/Math.pow(2, this.foldingFactor);

        const requiredAdditionalPoints = this.securityLevel-this.numColinearityChecks;
        const seed = proofStream.verifierFiatShamir();
        const additionalIndices = this.sampleIndices(
            seed,
            omegaDomainDividedByFoldingFactor,
            new Set(expandedFriPoints.map(e => e[0][0])),
            requiredAdditionalPoints
        );

        for(let index of additionalIndices) {
            const pointValues = proofStream.pullBigInts(this.byteLength);
            //console.log("boundaryQuotientAndTraceRoots, load opened points for polynomial: "+index+" load point: "+i);
            if(!MultiMerkleTree.verify(topFRIMerkleRoot, index, proofStream.pull(), pointValues, this.byteLength)) throw new Error("Invalid merkle path to additional FRI point provided");
            expandedFriPoints.push(pointValues.map((element, elementIndex) => {
                return [index + (omegaDomainDividedByFoldingFactor*elementIndex), element];
            }));
        }

        console.timeEnd("STARK.verify: Load additional FRI poly points");
        //console.log("Fri points: ", friPoints.map(point => point[0]));

        const pointOffsetSelectors = this.sampleNumbers(proofStream.verifierFiatShamir(), Math.pow(2, this.foldingFactor), this.securityLevel);

        //Boundary quotient / trace polynomial points
        const boundaryQuotientAndTracePoints: bigint[][] = Array<bigint[]>(this.numRegisters);
        const boundaryQuotientAndTracePointsPlus1: bigint[][] = Array<bigint[]>(this.numRegisters);

        for(let i=0;i<this.numRegisters;i++) {
            boundaryQuotientAndTracePoints[i] = Array<bigint>(expandedFriPoints.length);
            boundaryQuotientAndTracePointsPlus1[i] = Array<bigint>(expandedFriPoints.length);
        }

        console.time("STARK.verify: boundaryQuotientAndTraceRoots load");
        const friPoints = Array<[number, bigint]>(expandedFriPoints.length);
        expandedFriPoints.forEach((points, pointIndex) => {
            const point = points[pointOffsetSelectors[pointIndex]];

            const polynomialValues = proofStream.pullBigInts(this.byteLength);
            //console.log("boundaryQuotientAndTraceRoots, load opened points for polynomial: "+index+" load point: "+i);
            if(!MultiMerkleTree.verify(boundaryQuotientAndTraceRoot, point[0], proofStream.pull(), polynomialValues, this.byteLength)) throw new Error("Invalid merkle path to boundary quotient poly");

            const secondIndex = (point[0] + this.expansionFactor) % this.omegaDomain.length;
            const polynomialValuesPlus1 = proofStream.pullBigInts(this.byteLength);
            if(!MultiMerkleTree.verify(boundaryQuotientAndTraceRoot, secondIndex, proofStream.pull(), polynomialValuesPlus1, this.byteLength)) throw new Error("Invalid merkle path to boundary quotient poly (at i+1)");

            polynomialValues.forEach((value, index) => boundaryQuotientAndTracePoints[index][pointIndex] = value);
            polynomialValuesPlus1.forEach((value, index) => boundaryQuotientAndTracePointsPlus1[index][pointIndex] = value);

            friPoints[pointIndex] = point;
        });

        // boundaryQuotientAndTraceRoots.forEach((quotientOrTraceRoot, index) => {
        //
        //     //console.log("boundaryQuotientAndTraceRoots, load opened points for polynomial: ", index);
        //
        //     boundaryQuotientAndTracePoints[index] = Array<bigint>(friPoints.length);
        //     boundaryQuotientAndTracePointsPlus1[index] = Array<bigint>(friPoints.length);
        //
        //     //Verify opened leaves on boundaryQuotientAndTracePMTs
        //     friPoints.forEach((point, i) => {
        //         const polynomialValue = proofStream.pullBigInt();
        //         //console.log("boundaryQuotientAndTraceRoots, load opened points for polynomial: "+index+" load point: "+i);
        //         if(!MerkleTree.verify(boundaryQuotientAndTraceRoots[index], point[0], proofStream.pull(), polynomialValue, this.byteLength)) throw new Error("Invalid merkle path to boundary quotient poly");
        //
        //         const secondIndex = (point[0] + this.expansionFactor) % this.omegaDomain.length;
        //         const polynomialValuePlus1 = proofStream.pullBigInt();
        //         if(!MerkleTree.verify(boundaryQuotientAndTraceRoots[index], secondIndex, proofStream.pull(), polynomialValuePlus1, this.byteLength)) throw new Error("Invalid merkle path to boundary quotient poly (at i+1)");
        //
        //         boundaryQuotientAndTracePoints[index][i] = polynomialValue;
        //         boundaryQuotientAndTracePointsPlus1[index][i] = polynomialValuePlus1;
        //     });
        //
        // });
        console.timeEnd("STARK.verify: boundaryQuotientAndTraceRoots load");

        console.time("STARK.verify: Boundary polys");
        const boundaryInterpolants = this.boundaryInterpolants(boundaryConditions);
        const boundaryZerofiers = this.boundaryZerofiers(boundaryConditions);

        const boundaryQuotientDegreeBounds = this.boundaryQuotientDegreeBounds(boundaryZerofiers);
        console.timeEnd("STARK.verify: Boundary polys");

        console.time("STARK.verify: Transition zerofier");
        const transitionZerofier = this.transitionZerofier();
        console.timeEnd("STARK.verify: Transition zerofier");

        const transitionQuotientDegreeBounds = this.transitionQuotientDegreeBounds(this.transitionDegreeBounds(transitionConstraints));

        const transitionQuotientWeights: [bigint, bigint][] = transitionQuotientDegreeBounds.map((val, index) => {
            const buff = Buffer.alloc(6);
            buff.writeUIntBE(index, 0, 6);

            const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                buff,
                Buffer.from("00", "hex")
            ])).digest());

            const beta = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                buff,
                Buffer.from("01", "hex")
            ])).digest());

            return [alpha, beta];
        });

        const boundaryQuotientWeights: [bigint, bigint][] = boundaryQuotientDegreeBounds.map((val, index) => {
            const buff = Buffer.alloc(6);
            buff.writeUIntBE(index, 0, 6);

            const alpha = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                buff,
                Buffer.from("02", "hex")
            ])).digest());

            const beta = this.field.prng(crypto.createHash("sha256").update(Buffer.concat([
                entropy,
                buff,
                Buffer.from("03", "hex")
            ])).digest());

            return [alpha, beta];
        });

        console.time("STARK.verify: Probabilistic checks");
        //Check every point
        friPoints.forEach((friPoint, pointIndex) => {

            /**
             * FRI point contains randomly weighted combination of:
             *  - boundary quotients / traces - Qb / P
             *  Qb(x) = (P(x) - B(x)) / Nb(x) =>
             *      P(x) = Qb(x) * Nb(x) + B(x)
             *
             *  - transition quotients - Qt
             *  Qt(x) = M(x, P1i(x), P2i(x), ..., P1i+1(x), P2i+1(x), ...) / Nt(x)
             *
             */

            const i = friPoint[0];
            const x = this.field.mul(this.friOffset, this.omegaDomain[i]);

            const iPlus1 = (friPoint[0] + this.expansionFactor) % this.omegaDomain.length;
            const xPlus1 = this.field.mul(this.friOffset, this.omegaDomain[iPlus1]);

            let traces = Array<bigint>(this.numRegisters);
            let tracesPlus1 = Array<bigint>(this.numRegisters);
            //Reconstruct original traces from boundary quotients
            boundaryInterpolants.forEach((boundaryInterpolant, register) => {
                if(boundaryInterpolant==null) {

                    traces[register] = boundaryQuotientAndTracePoints[register][pointIndex];
                    tracesPlus1[register] = boundaryQuotientAndTracePointsPlus1[register][pointIndex];

                } else {

                    const trace = this.field.add(
                        this.field.mul(
                            boundaryQuotientAndTracePoints[register][pointIndex],
                            boundaryZerofiers[register].evaluate(x)
                        ),
                        boundaryInterpolant.evaluate(x)
                    );
                    const tracePlus1 = this.field.add(
                        this.field.mul(
                            boundaryQuotientAndTracePointsPlus1[register][pointIndex],
                            boundaryZerofiers[register].evaluate(xPlus1)
                        ),
                        boundaryInterpolant.evaluate(xPlus1)
                    );

                    traces[register] = trace;
                    tracesPlus1[register] = tracePlus1;
                }
            });

            const multivariantPoint = [x].concat(
                traces,
                tracesPlus1
            );

            //Evaluate transition polynomial
            const transitionPolynomialValues = transitionConstraints.map(constraint => {
                return constraint.evaluate(multivariantPoint);
            });

            const transitionQuotientValues: bigint[] = transitionPolynomialValues.map(val => this.field.div(val, transitionZerofier.evaluate(x)));

            let resultingPoint = 0n;

            transitionQuotientValues.forEach((transitionQuotientValue, transitionIndex) => {

                const addVal = this.field.mul(
                    this.field.add(
                        transitionQuotientWeights[transitionIndex][0],
                        this.field.mul(
                            transitionQuotientWeights[transitionIndex][1],
                            this.field.exp(x, BigInt(this.omicronDomain.length-transitionQuotientDegreeBounds[transitionIndex]-1))
                        )
                    ),
                    transitionQuotientValue
                );

                resultingPoint = this.field.add(resultingPoint, addVal);

            });

            boundaryQuotientAndTracePoints.forEach((boundaryQuotientAndTraceValues, boundaryIndex) => {

                const boundaryQuotientAndTraceValue = boundaryQuotientAndTraceValues[pointIndex];

                let degreeBounds = boundaryQuotientDegreeBounds[boundaryIndex];
                if(degreeBounds==null) {
                    degreeBounds = this.numCycles-1;
                }

                const addVal = this.field.mul(
                    this.field.add(
                        boundaryQuotientWeights[boundaryIndex][0],
                        this.field.mul(
                            boundaryQuotientWeights[boundaryIndex][1],
                            this.field.exp(x, BigInt(this.omicronDomain.length-degreeBounds-1))
                        )
                    ),
                    boundaryQuotientAndTraceValue
                );

                resultingPoint = this.field.add(resultingPoint, addVal);

            });

            // console.log("Traces at "+i, traces);
            // console.log("Traces+1 at "+i, tracesPlus1);
            // console.log("Constraint polynomials at "+i, transitionPolynomialValues);
            // console.log("Transition quotients at "+i, transitionQuotientValues);
            // console.log("Boundary quotients at "+i, boundaryQuotientAndTracePoints.map(val => val[pointIndex]));

            if(friPoint[1]!==resultingPoint) throw new Error("Invalid combined FRI point, got: "+friPoint[1]+", expected: "+resultingPoint+"!");

        });
        console.timeEnd("STARK.verify: Probabilistic checks");

    }

}