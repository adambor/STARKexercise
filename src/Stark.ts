import {FiniteField} from "@guildofweavers/galois";
import {MultiPolynomial} from "./polynomial/MultiPolynomial";
import {Polynomial} from "./polynomial/Polynomial";
import {ProofStream} from "./fiatshamir/ProofStream";
import {MerkleTree} from "./merkle/MerkleTree";
import * as crypto from "crypto";
import {Fri} from "./fri/Fri";

export type BoundaryConditions = Map<number, {
    cycle: number,
    value: bigint
}[]>;

export class Stark {

    field: FiniteField;
    byteLength: number;

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

    constructor(
        field: FiniteField,
        byteLength: number,
        expansionFactor: number,
        securityLevel: number,
        numRegisters: number,
        numCycles: number,
        transitionConstraintsDegree: number,
        friOffset: bigint
    ) {

        this.field = field;
        this.byteLength = byteLength;
        this.expansionFactor = expansionFactor;
        this.numColinearityChecks = securityLevel/2;
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
        return Polynomial.zerofier(this.omicronDomain.slice(0, this.numCycles-1), this.field);
    }

    boundaryZerofiers(points: BoundaryConditions): Polynomial[] {
        const boundaryZerofiers = Array<Polynomial>(this.numRegisters);
        for(let i=0;i<this.numRegisters;i++) {
            const registerPoints = points.get(i);
            if(registerPoints==null) {
                boundaryZerofiers[i] = null;
                continue;
            }
            boundaryZerofiers[i] = Polynomial.zerofier(registerPoints.map(val => this.omicronDomain[val.cycle]), this.field);
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
        const tracePolynomials: Polynomial[] = trace.map(values => Polynomial.interpolateDomain(executionDomain, values, this.field));

        const boundaryInterpolants = this.boundaryInterpolants(boundaryConditions);
        const boundaryZerofiers = this.boundaryZerofiers(boundaryConditions);

        //Obtain trace polynomial codewords
        const traceCodewords: bigint[][] = tracePolynomials.map(poly => poly.evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset));
        const traceCodewordsPlus1: bigint[][] = tracePolynomials.map(poly => poly.scale(this.omicron).evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset));

        //Boundary zerofier and interpolants codewords
        const boundaryInterpolantsCodewords: bigint[][] = boundaryInterpolants.map(poly => poly==null ? null : poly.evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset));
        const boundaryZerofiersCodewords: bigint[][] = boundaryZerofiers.map(poly => poly==null ? null : poly.evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset));

        //Obtain quotient codewords
        const boundaryQuotientCodewords: bigint[][] = traceCodewords.map((codeword, registerIndex) => {
            const boundaryInterpolantCodeword = boundaryInterpolantsCodewords[registerIndex];
            const boundaryZerofiersCodeword = boundaryZerofiersCodewords[registerIndex];

            if(boundaryInterpolantCodeword==null) return null;

            /**
             * f - trace
             * B - boundary interpolant
             * Zb - boundary zerofier
             *
             * (f(x)-B(x)) / Zb(x)
             */
            return codeword.map((value, index) => {
                return this.field.div(
                    this.field.sub(value, boundaryInterpolantCodeword[index]),
                    boundaryZerofiersCodeword[index]
                )
            });
        });

        if(runChecks) {
            const boundaryQuotientPolys = boundaryQuotientCodewords.map(codeword => codeword==null ? null : Polynomial.interpolateDomain(this.omegaDomain.map(omegaPower => this.field.mul(omegaPower, this.friOffset)), codeword, this.field))
            const boundaryQuotientPolyDegrees = boundaryQuotientPolys.map(poly => poly==null ? null : poly.degree());
            console.log("Boundary quotient poly degrees: ", boundaryQuotientPolyDegrees);
            console.log("Expected boundary quotient poly degrees: ", this.boundaryQuotientDegreeBounds(boundaryZerofiers));
        }

        //Map boundary quotient codewords (use raw traces for registries without boundary constraints) to PMTs
        const boundaryQuotientAndTracePMTs = boundaryQuotientCodewords.map((codeword, index) => codeword==null ? new MerkleTree(traceCodewords[index], this.byteLength) : new MerkleTree(codeword, this.byteLength));

        //Commit boundary quotients & possibly traces
        boundaryQuotientAndTracePMTs.forEach(pmt => {
            proofStream.push(pmt.commit());
        });

        //Transition zerofier Zt - value of 0 on point 0...this.numCycles-1
        const transitionZerofierCodewords = this.transitionZerofier().evaluateAtRootsWithOffset(this.omegaDomain, this.friOffset);

        //Evaluate transition codewords - evaluation of multivariant polynomials Mt(x, P1i, P2i, ..., P1i+1, P2i+1, ...)
        const transitionCodewords: bigint[][] = transitionConstraints.map(transitionPolynomial => {
            return this.omegaDomain.map((omegaPower, i) => {
                const x = this.field.mul(omegaPower, this.friOffset);
                return transitionPolynomial.evaluate(
                    [x].concat(
                        traceCodewords.map(codeword => codeword[i]),
                        traceCodewordsPlus1.map(codeword => codeword[i])
                    )
                );
            });
        });

        /**
         * Mt - transition multivariant polynomial
         * Zt - transition zerofier
         *
         * Mt(x, P1i, P2i, ..., P1i+1, P2i+1, ...) / Zb(x)
         */
        const transitionQuotientCodewords: bigint[][] = transitionCodewords.map(codeword => {
            return codeword.map((value, i) => this.field.div(value, transitionZerofierCodewords[i]));
        });

        const entropy = proofStream.proverFiatShamir();

        //Get degree bounds for respective transition quotients, these depend on the degree of the transition constraints
        const transitionQuotientDegreeBounds = this.transitionQuotientDegreeBounds(this.transitionDegreeBounds(transitionConstraints));

        if(runChecks) {
            const transitionQuotientPolys = transitionQuotientCodewords.map(codeword => codeword==null ? null : Polynomial.interpolateDomain(this.omegaDomain.map(omegaPower => this.field.mul(omegaPower, this.friOffset)), codeword, this.field))
            const transitionQuotientPolyDegrees = transitionQuotientPolys.map(poly => poly==null ? null : poly.degree());
            console.log("Boundary quotient poly degrees: ", transitionQuotientPolyDegrees);
            console.log("Expected boundary quotient poly degrees: ", transitionQuotientDegreeBounds);
        }

        //Construct FRI codeword of random weighted combinations of polys to be proven.
        const friCodeword = Array<bigint>(this.omicronDomain.length);

        //Transition quotients
        transitionQuotientCodewords.forEach((codeword, index) => {

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

            codeword.forEach((fX, i) => {
                if(friCodeword[i]==null) friCodeword[i] = 0n;

                const x = this.field.mul(this.friOffset, this.omegaDomain[i]);
                const addVal = this.field.mul(
                    this.field.add(
                        alpha,
                        this.field.mul(
                            beta,
                            this.field.exp(x, BigInt(this.omicronDomain.length-transitionQuotientDegreeBounds[index]-1))
                        )
                    ),
                    fX
                );

                friCodeword[i] = this.field.add(friCodeword[i], addVal);
            });

        });

        let boundaryQuotientDegreeBounds = this.boundaryQuotientDegreeBounds(boundaryZerofiers);

        //Boundary quotients
        boundaryQuotientCodewords.forEach((codeword, index) => {

            let degreeBounds = boundaryQuotientDegreeBounds[index];
            if(codeword==null) {
                codeword = traceCodewords[index];
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

            codeword.forEach((fX, i) => {
                if(friCodeword[i]==null) friCodeword[i] = 0n;

                const x = this.field.mul(this.friOffset, this.omegaDomain[i]);
                const addVal = this.field.mul(
                    this.field.add(
                        alpha,
                        this.field.mul(
                            beta,
                            this.field.exp(x, BigInt(this.omicronDomain.length-degreeBounds-1))
                        )
                    ),
                    fX
                );

                friCodeword[i] = this.field.add(friCodeword[i], addVal);
            });

        });

        const fri = new Fri(this.friOffset, this.omega, this.omegaDomain.length, this.field, this.expansionFactor, this.numColinearityChecks);
        const sampledPoints = fri.prove(friCodeword, proofStream, this.byteLength);

        //console.log("Fri points: ", sampledPoints);

        //Open up leaves on the boundary quotients/trace polys
        boundaryQuotientAndTracePMTs.forEach(codeword => {
            sampledPoints.forEach(i => {
                {
                    proofStream.pushBigInt(codeword.leafs[i], this.byteLength);
                    proofStream.push(codeword.openBuffer(i));

                    const secondIndex = (i + this.expansionFactor) % this.omegaDomain.length;
                    proofStream.pushBigInt(codeword.leafs[secondIndex], this.byteLength);
                    proofStream.push(codeword.openBuffer(secondIndex));
                }

                i = i + this.omegaDomain.length/2;

                {
                    proofStream.pushBigInt(codeword.leafs[i], this.byteLength);
                    proofStream.push(codeword.openBuffer(i));

                    const secondIndex = (i + this.expansionFactor) % this.omegaDomain.length;
                    proofStream.pushBigInt(codeword.leafs[secondIndex], this.byteLength);
                    proofStream.push(codeword.openBuffer(secondIndex));
                }
            });
        });

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

        const boundaryQuotientAndTraceRoots = Array<Buffer>(this.numRegisters);
        for(let i=0;i<this.numRegisters;i++) {
            boundaryQuotientAndTraceRoots[i] = proofStream.pull();
        }

        //console.log("boundaryQuotientAndTraceRoots", boundaryQuotientAndTraceRoots);

        const entropy = proofStream.verifierFiatShamir();

        //Run FRI
        const fri = new Fri(this.friOffset, this.omega, this.omegaDomain.length, this.field, this.expansionFactor, this.numColinearityChecks);
        const friPoints = fri.verify(proofStream, this.byteLength);

        //console.log("Fri points: ", friPoints.map(point => point[0]));

        //Boundary quotient / trace polynomial points
        const boundaryQuotientAndTracePoints: bigint[][] = Array<bigint[]>(this.numRegisters);
        const boundaryQuotientAndTracePointsPlus1: bigint[][] = Array<bigint[]>(this.numRegisters);

        boundaryQuotientAndTraceRoots.forEach((quotientOrTraceRoot, index) => {

            //console.log("boundaryQuotientAndTraceRoots, load opened points for polynomial: ", index);

            boundaryQuotientAndTracePoints[index] = Array<bigint>(friPoints.length);
            boundaryQuotientAndTracePointsPlus1[index] = Array<bigint>(friPoints.length);

            //Verify opened leaves on boundaryQuotientAndTracePMTs
            friPoints.forEach((point, i) => {
                const polynomialValue = proofStream.pullBigInt();
                //console.log("boundaryQuotientAndTraceRoots, load opened points for polynomial: "+index+" load point: "+i);
                if(!MerkleTree.verify(boundaryQuotientAndTraceRoots[index], point[0], proofStream.pull(), polynomialValue, this.byteLength)) throw new Error("Invalid merkle path to boundary quotient poly");

                const secondIndex = (point[0] + this.expansionFactor) % this.omegaDomain.length;
                const polynomialValuePlus1 = proofStream.pullBigInt();
                if(!MerkleTree.verify(boundaryQuotientAndTraceRoots[index], secondIndex, proofStream.pull(), polynomialValuePlus1, this.byteLength)) throw new Error("Invalid merkle path to boundary quotient poly (at i+1)");

                boundaryQuotientAndTracePoints[index][i] = polynomialValue;
                boundaryQuotientAndTracePointsPlus1[index][i] = polynomialValuePlus1;
            });

        });

        const boundaryInterpolants = this.boundaryInterpolants(boundaryConditions);
        const boundaryZerofiers = this.boundaryZerofiers(boundaryConditions);

        const boundaryQuotientDegreeBounds = this.boundaryQuotientDegreeBounds(boundaryZerofiers);

        const transitionZerofier = this.transitionZerofier();

        const transitionQuotientDegreeBounds = this.transitionQuotientDegreeBounds(this.transitionDegreeBounds(transitionConstraints));

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

                const buff = Buffer.alloc(6);
                buff.writeUIntBE(transitionIndex, 0, 6);

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

                const addVal = this.field.mul(
                    this.field.add(
                        alpha,
                        this.field.mul(
                            beta,
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

                const buff = Buffer.alloc(6);
                buff.writeUIntBE(boundaryIndex, 0, 6);

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

                const addVal = this.field.mul(
                    this.field.add(
                        alpha,
                        this.field.mul(
                            beta,
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

    }

}