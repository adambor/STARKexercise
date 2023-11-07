import {BoundaryConditions, Stark} from "../Stark";
import {FiniteField} from "@guildofweavers/galois";
import {ProofStream} from "../fiatshamir/ProofStream";
import {MultiPolynomial} from "../polynomial/MultiPolynomial";

const TRANSITION_CONSTRAINTS = [
    new Map<bigint[], bigint>([
        [[0n, 0n, 0n, 0n, 1n], 1n],
        [[0n, 1n, 0n, 0n, 0n], -1n]
    ]),
    new Map<bigint[], bigint>([
        [[0n, 0n, 0n, 1n, 0n], 1n],
        [[0n, 1n, 0n, 0n, 0n], -1n],
        [[0n, 0n, 1n, 0n, 0n], -1n]
    ])
];

export class Fibonacci {

    field: FiniteField;
    fieldGenerator: bigint;
    byteLength: number;
    expansionFactor: number;
    securityLevel: number;

    transitionConstraints: MultiPolynomial[];

    constructor(
        field: FiniteField,
        fieldGenerator: bigint,
        byteLength: number,
        expansionFactor: number,
        securityLevel: number
    ) {

        this.field = field;
        this.fieldGenerator = fieldGenerator;
        this.byteLength = byteLength;
        this.expansionFactor = expansionFactor;
        this.securityLevel = securityLevel;

        this.transitionConstraints = TRANSITION_CONSTRAINTS.map(data => new MultiPolynomial(data, this.field));

    }

    prove(index: number, runChecks?: boolean): {
        output: bigint,
        proof: ProofStream
    } {

        const stark = new Stark(this.field, this.byteLength, this.expansionFactor, this.securityLevel, 2, index-1, 1, this.fieldGenerator);

        let vars = [1n, 1n];

        const traces: bigint[][] = Array<bigint[]>(vars.length);
        for(let i=0;i<vars.length;i++) {
            traces[i] = [];
        }

        traces[0].push(vars[0]);
        traces[1].push(vars[1]);

        for(let i=0;i<index-2;i++) {
            vars = [vars[1]+vars[0], vars[0]];
            traces[0].push(vars[0]);
            traces[1].push(vars[1]);
        }

        const boundaryConditions: BoundaryConditions = new Map([
            [0, [{cycle: 0, value: 1n}, {cycle: index-2, value: vars[0]}]],
            [1, [{cycle: 0, value: 1n}]]
        ]);

        console.log("result=",vars[0])

        const proofStream = new ProofStream([]);
        stark.prove(traces, this.transitionConstraints, boundaryConditions, proofStream, runChecks);

        return {
            output: vars[0],
            proof: proofStream
        };

    }

}