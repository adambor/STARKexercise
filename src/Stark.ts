import {FiniteField} from "@guildofweavers/galois";
import {MultiPolynomial} from "./polynomial/MultiPolynomial";
import {Polynomial} from "./polynomial/Polynomial";

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

    boundaryZerofiers(points: Map<number, {
        cycle: number,
        value: bigint
    }[]>) {
        const boundaryZerofiers = Array<Polynomial>(this.numRegisters);
        for(let i=0;i<this.numRegisters;i++) {
            const registerPoints = points.get(i);
            boundaryZerofiers[i] = Polynomial.zerofier(registerPoints.map(val => this.omicronDomain[val.cycle]), this.field);
        }
    }

}