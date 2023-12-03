import {BoundaryConditions, Stark} from "../Stark";
import {FiniteField} from "@guildofweavers/galois";
import {ProofStream} from "../fiatshamir/ProofStream";
import {MultiPolynomial} from "../polynomial/MultiPolynomial";
import {FastStark} from "../FastStark";
import {Polynomial} from "../polynomial/Polynomial";

/*
Registers:
    - bits num 1
    - sum num 1
    - bits num 2
    - sum num 2
    - enable flag
 */

/*
num1 > num2:
enableFlag: starts at 1
if enableFlag then bitNum1 - bitNum2 = 1/0
if enableFlag then enableFlag = enableFlag - (bitNum1 - bitNum2)
 */

const TRANSITION_CONSTRAINTS = [
    new Map<bigint[], bigint>([
        [[0n,   2n, 0n, 0n, 0n, 0n,     0n, 0n, 0n, 0n, 0n], 1n],
        [[0n,   1n, 0n, 0n, 0n, 0n,     0n, 0n, 0n, 0n, 0n], -1n]
    ]), //Constaint bits (num 1) to 0 or 1 => (x0-1)x0 = x0^2 - x0
    new Map<bigint[], bigint>([
        [[0n,   0n, 0n, 2n, 0n, 0n,     0n, 0n, 0n, 0n, 0n], 1n],
        [[0n,   0n, 0n, 1n, 0n, 0n,     0n, 0n, 0n, 0n, 0n], -1n]
    ]), //Constaint bits (num 2) to 0 or 1 => (x2-1)x2 = x2^2 - x2
    new Map<bigint[], bigint>([
        [[0n,   2n, 0n, 0n, 0n, 1n,     0n, 0n, 0n, 0n, 0n], 1n],
        [[0n,   1n, 0n, 1n, 0n, 1n,     0n, 0n, 0n, 0n, 0n], -2n],
        [[0n,   0n, 0n, 2n, 0n, 1n,     0n, 0n, 0n, 0n, 0n], 1n],
        [[0n,   1n, 0n, 0n, 0n, 1n,     0n, 0n, 0n, 0n, 0n], -1n],
        [[0n,   0n, 0n, 1n, 0n, 1n,     0n, 0n, 0n, 0n, 0n], 1n],
    ]), //if enableFlag then bitNum1 - bitNum2 = 1/0
    new Map<bigint[], bigint>([
        [[0n,   0n, 0n, 0n, 0n, 1n,     0n, 0n, 0n, 0n, 0n], 1n],
        [[0n,   1n, 0n, 0n, 0n, 1n,     0n, 0n, 0n, 0n, 0n], -1n],
        [[0n,   0n, 0n, 1n, 0n, 1n,     0n, 0n, 0n, 0n, 0n], 1n],
        [[0n,   0n, 0n, 0n, 0n, 0n,     0n, 0n, 0n, 0n, 1n], -1n]
    ]), //if enableFlag then enableFlag = enableFlag - (bitNum1 - bitNum2)
];

export class NumCompare {

    field: FiniteField;
    fieldGenerator: bigint;
    byteLength: number;
    expansionFactor: number;
    securityLevel: number;
    foldingFactor: number;

    constructor(
        field: FiniteField,
        fieldGenerator: bigint,
        byteLength: number,
        expansionFactor: number,
        securityLevel: number,
        foldingFactor: number
    ) {

        this.field = field;
        this.fieldGenerator = fieldGenerator;
        this.byteLength = byteLength;
        this.expansionFactor = expansionFactor;
        this.securityLevel = securityLevel;
        this.foldingFactor = foldingFactor;

    }

    prove(num1: bigint, num2: bigint, bitLength: number, runChecks?: boolean): {
        proof: ProofStream
    } {

        const stark = new FastStark(this.field, this.byteLength, this.expansionFactor, this.securityLevel, 5, bitLength+1, 3, this.fieldGenerator, this.foldingFactor);

        console.log("Unexpanded omicron len: ", stark.unexpandedOmicronDomain.length);
        console.log("Omicron len: ", stark.omicronDomain.length);
        console.log("Omega len: ", stark.omegaDomain.length);
        console.log("Unexpanded omicron: ", stark.unexpandedOmicron);
        console.log("Omicron^omicron expansion: ", this.field.exp(stark.omicron, BigInt(stark.omicronExpansionFactor)));

        const powersOf2 = this.field.getPowerSeries(2n, bitLength).toValues().reverse().concat(0n);

        const powersOf2Poly = Polynomial.interpolateDomain(stark.unexpandedOmicronDomain, powersOf2, this.field);

        //Create summand for num 1
        const num1Summand = new MultiPolynomial(new Map<bigint[], bigint>([
            [[0n,   0n, 1n, 0n, 0n, 0n,    0n, 0n, 0n, 0n, 0n], 1n],
            [[0n,   0n, 0n, 0n, 0n, 0n,    0n, 1n, 0n, 0n, 0n], -1n]
        ]), this.field).add(
            MultiPolynomial.lift(powersOf2Poly, 0).mul(
                MultiPolynomial.lift(new Polynomial(this.field.newVectorFrom([0n, 1n]), this.field), 1)
            )
        ); //Summand for num 1

        //Create summand for num 1
        const num2Summand = new MultiPolynomial(new Map<bigint[], bigint>([
            [[0n,   0n, 0n, 0n, 1n, 0n,    0n, 0n, 0n, 0n, 0n], 1n],
            [[0n,   0n, 0n, 0n, 0n, 0n,    0n, 0n, 0n, 1n, 0n], -1n]
        ]), this.field).add(
            MultiPolynomial.lift(powersOf2Poly, 0).mul(
                MultiPolynomial.lift(new Polynomial(this.field.newVectorFrom([0n, 1n]), this.field), 3)
            )
        ); //Summand for num 2

        const transitionConstraints = TRANSITION_CONSTRAINTS
            .map(data => new MultiPolynomial(data, this.field))
            .concat(num1Summand, num2Summand);

        const num1Binary = num1.toString(2).padStart(bitLength, "0")+"0";
        const num2Binary = num2.toString(2).padStart(bitLength, "0")+"0";

        const registers = 5;

        const traces: bigint[][] = Array<bigint[]>(registers);
        for(let i=0;i<registers;i++) {
            traces[i] = [];
        }

        const sums: [bigint, bigint] = [0n, 0n];

        let enableFlag = 1n;

        for(let i=0;i<bitLength+1;i++) {
            const bit1 = BigInt(num1Binary.charAt(i));
            traces[0].push(bit1);
            const bit1Mul = this.field.mul(bit1, powersOf2[i]);

            const bit2 = BigInt(num2Binary.charAt(i));
            traces[2].push(bit2);
            const bit2Mul = this.field.mul(bit2, powersOf2[i]);

            traces[1].push(sums[0]);
            traces[3].push(sums[1]);
            traces[4].push(enableFlag);

            console.log("Sum1: ", sums[0]);
            console.log("Sum2: ", sums[1]);
            console.log("enableFlag: ", enableFlag);
            console.log("bit1-bit2: ", bit1-bit2);

            sums[0] = this.field.add(sums[0], bit1Mul);
            sums[1] = this.field.add(sums[1], bit2Mul);

            if(bit1>bit2) enableFlag = 0n;
        }

        const boundaryConditions: BoundaryConditions = new Map([
            [0, [{cycle: bitLength, value: 0n}]],
            [1, [{cycle: 0, value: 0n}, {cycle: bitLength, value: num1}]],
            [2, [{cycle: bitLength, value: 0n}]],
            [4, [{cycle: 0, value: 1n}, {cycle: bitLength, value: 0n}]]
        ]);

        const proofStream = new ProofStream([]);
        stark.prove(traces, transitionConstraints, boundaryConditions, proofStream, runChecks);

        return {
            proof: proofStream
        };

    }

    verify(num1: bigint, bitLength: number, proof: ProofStream) {

        const stark = new FastStark(this.field, this.byteLength, this.expansionFactor, this.securityLevel, 5, bitLength+1, 3, this.fieldGenerator, this.foldingFactor);

        const powersOf2 = this.field.getPowerSeries(2n, bitLength).toValues().reverse().concat(0n);

        const powersOf2Poly = Polynomial.interpolateDomain(stark.unexpandedOmicronDomain, powersOf2, this.field);

        //Create summand for num 1
        const num1Summand = new MultiPolynomial(new Map<bigint[], bigint>([
            [[0n,   0n, 1n, 0n, 0n, 0n,    0n, 0n, 0n, 0n, 0n], 1n],
            [[0n,   0n, 0n, 0n, 0n, 0n,    0n, 1n, 0n, 0n, 0n], -1n]
        ]), this.field).add(
            MultiPolynomial.lift(powersOf2Poly, 0).mul(
                MultiPolynomial.lift(new Polynomial(this.field.newVectorFrom([0n, 1n]), this.field), 1)
            )
        ); //Summand for num 1

        //Create summand for num 1
        const num2Summand = new MultiPolynomial(new Map<bigint[], bigint>([
            [[0n,   0n, 0n, 0n, 1n, 0n,    0n, 0n, 0n, 0n, 0n], 1n],
            [[0n,   0n, 0n, 0n, 0n, 0n,    0n, 0n, 0n, 1n, 0n], -1n]
        ]), this.field).add(
            MultiPolynomial.lift(powersOf2Poly, 0).mul(
                MultiPolynomial.lift(new Polynomial(this.field.newVectorFrom([0n, 1n]), this.field), 3)
            )
        ); //Summand for num 2

        const transitionConstraints = TRANSITION_CONSTRAINTS
            .map(data => new MultiPolynomial(data, this.field))
            .concat(num1Summand, num2Summand);

        const boundaryConditions: BoundaryConditions = new Map([
            [0, [{cycle: bitLength, value: 0n}]],
            [1, [{cycle: 0, value: 0n}, {cycle: bitLength, value: num1}]],
            [2, [{cycle: bitLength, value: 0n}]],
            [4, [{cycle: 0, value: 1n}, {cycle: bitLength, value: 0n}]]
        ]);

        stark.verify(proof, transitionConstraints, boundaryConditions);

    }

}