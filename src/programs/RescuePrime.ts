import {FiniteField} from "@guildofweavers/galois";
import {createHash} from "crypto";
import {MultiPolynomial} from "../polynomial/MultiPolynomial";
import {bufferToBigInt} from "../merkle/MerkleTree";
import {Polynomial} from "../polynomial/Polynomial";
import {ProofStream} from "../fiatshamir/ProofStream";
import {BoundaryConditions, Stark} from "../Stark";



function leadingCofficient(vector: bigint[]): bigint {

    for(let i=0;i<vector.length;i++) {
        if(vector[i]!==0n) return vector[i];
    }

}

function scaleAndSub(vecA: bigint[], vecAconst: bigint, vecB: bigint[], field: FiniteField) {

    return vecA.map((_, index) => field.sub(vecB[index], field.mul(vecA[index], vecAconst)));

}

function invMatrix(matrix: bigint[][], field: FiniteField) {

    const multiplicant = field.inv(field.sub(
        field.mul(matrix[0][0], matrix[1][1]),
        field.mul(matrix[0][1], matrix[1][0])
    ));

    return [
        [field.mul(matrix[1][1], multiplicant), field.neg(field.mul(matrix[0][1], multiplicant))],
        [field.neg(field.mul(matrix[1][0], multiplicant)), field.mul(matrix[0][0], multiplicant)],
    ]

}

export class RescuePrime {


    field: FiniteField;
    fieldModulus: bigint;
    fieldGenerator: bigint;
    byteLength: number;
    expansionFactor: number;
    securityLevel: number;

    m: number;
    alpha: bigint;
    rounds: number;

    mdsMatrix: bigint[][];
    mdsMatrixInv: bigint[][];
    roundConstants: bigint[];
    alphainv: bigint;

    getMDSMatrix() {

        const mdsMatrix: bigint[][] = [];

        for(let i=0;i<this.m;i++) {
            mdsMatrix[i] = [];
            for(let j=0;j<2*this.m;j++) {
                mdsMatrix[i][j] = this.field.exp(this.fieldGenerator, BigInt((j)*(i)));
            }
        }

        for(let i=0;i<mdsMatrix.length;i++) {
            for(let j=i+1;j<mdsMatrix.length;j++) {
                const multiplier = this.field.div(leadingCofficient(mdsMatrix[j]), leadingCofficient(mdsMatrix[i]));
                mdsMatrix[j] = scaleAndSub(mdsMatrix[i], multiplier, mdsMatrix[j], this.field);
            }
        }

        const resultMatrix: bigint[][] = [];

        for(let i=0;i<this.m;i++) {
            //Row
            for(let j=0;j<this.m;j++) {
                //Column
                if(resultMatrix[j]==null) resultMatrix[j] = [];
                resultMatrix[j][i] = mdsMatrix[i][this.m+j];
            }
        }


        return resultMatrix;

    }

    getRoundConstants() {

        const numBytes = this.byteLength * 2 * this.m * this.rounds;
        const seedString = "Rescue-XLIX("+this.fieldModulus+","+this.m+","+1+","+this.securityLevel+")";
        const bytes = createHash("shake256", {
            outputLength: numBytes
        }).update(seedString).digest();

        const roundConstants: bigint[] = [];
        for(let i=0;i<2*this.m*this.rounds;i++) {
            roundConstants.push(bufferToBigInt(bytes.subarray(i*this.byteLength, (i+1)*this.byteLength)) % this.fieldModulus);
        }

        return roundConstants;

    }

    interpolateRoundConstantsPolys(omicronDomain: bigint[]): {firstStepPolys: Polynomial[], secondStepPolys: Polynomial[]} {

        const zerofierCache = {};
        const firstStepPolys = [];
        const secondStepPolys = [];
        for(let i=0;i<this.m;i++) {
            const firstStepPoly = Polynomial.fastFFTInterpolate(omicronDomain, this.roundConstants.filter((_, index) => index%(2*this.m)===i), this.field, null, null, zerofierCache);
            const secondStepPoly = Polynomial.fastFFTInterpolate(omicronDomain, this.roundConstants.filter((_, index) => index%(2*this.m)===this.m+i), this.field, null, null, zerofierCache);

            firstStepPolys.push(firstStepPoly);
            secondStepPolys.push(secondStepPoly);
        }

        return {
            firstStepPolys,
            secondStepPolys
        }

    }

    getTransitionConstraints(omicronDomain: bigint[], field: FiniteField): MultiPolynomial[] {

        const transitionConstraints = [];

        const constantPolys = this.interpolateRoundConstantsPolys(omicronDomain);
        for(let i=0;i<this.m;i++) {

            const map = new Map<bigint[], bigint>();
            let rhs = MultiPolynomial.zero(field);
            const secondMConstants = MultiPolynomial.lift(constantPolys.secondStepPolys[i], 0);
            for(let j=0;j<this.m;j++) {
                const arr = [];
                arr[1+j] = this.alpha;
                arr.fill(0n, 0, j);
                map.set(arr, this.mdsMatrix[i][j]);

                const arr2 = [];
                arr2[1+this.m+j] = 1n;
                arr2.fill(0n, 0, this.m+j);
                rhs = rhs.add(
                    new MultiPolynomial(new Map<bigint[], bigint>([[arr2, 1n]]), field).sub(
                        secondMConstants
                    ).mulByConstant(this.mdsMatrixInv[i][j])
                );
            }
            const lhs = new MultiPolynomial(map, field).add(MultiPolynomial.lift(constantPolys.firstStepPolys[i], 0));
            rhs = rhs.power(this.alpha);



            transitionConstraints.push(lhs.sub(rhs));

        }

        return transitionConstraints;

    }

    constructor(
        field: FiniteField,
        fieldModulus: bigint,
        fieldGenerator: bigint,
        byteLength: number,
        expansionFactor: number,
        securityLevel: number,

        m: number,
        alpha: bigint,
        rounds: number,
    ) {

        this.field = field;
        this.fieldModulus = fieldModulus;
        this.fieldGenerator = fieldGenerator;
        this.byteLength = byteLength;
        this.expansionFactor = expansionFactor;
        this.securityLevel = securityLevel;

        this.m = m;
        this.alpha = alpha;
        this.rounds = rounds;

        this.roundConstants = this.getRoundConstants();
        this.mdsMatrix = this.getMDSMatrix();
        this.alphainv = field.inv(alpha);

        if(this.m!==2) throw new Error("Matrix inversion algorithm only implemented for 2x2 matrices!");
        this.mdsMatrixInv = invMatrix(this.mdsMatrix, field);

    }

    hash(input: bigint, traces?: bigint[][]): bigint {

        let state = [];
        state[this.m-1] = 0n;
        state.fill(0n, 0, this.m);
        state[0] = input;

        if(traces!=null) for(let i=0;i<this.m;i++) {
            traces[i] = [];
        }

        if(traces!=null) state.forEach((val, index) => traces[index].push(val));

        for(let i=0;i<this.rounds;i++) {

            state = state.map(val => this.field.exp(val, this.alpha));

            const temp1 = this.mdsMatrix.map((row, index) => {
                let result = 0n;
                for(let j=0;j<this.m;j++) {
                    result = this.field.add(result, this.field.mul(row[j], state[j]));
                }
                return result;
            });

            state = temp1.map((val, index) => this.field.add(val, this.roundConstants[(2*i*this.m) + index]));

            state = state.map(val => this.field.exp(val, this.alphainv));

            const temp2 = this.mdsMatrix.map((row, index) => {
                let result = 0n;
                for(let j=0;j<this.m;j++) {
                    result = this.field.add(result, this.field.mul(row[j], state[j]));
                }
                return result;
            });

            state = temp2.map((val, index) => this.field.add(val, this.roundConstants[(2*i*this.m) + this.m + index]));

            if(traces!=null) state.forEach((val, index) => traces[index].push(val));

        }

        return state[0];

    }

    prove(input: bigint, runChecks?: boolean): {
        output: bigint,
        proof: ProofStream
    } {

        const traces: bigint[][] = [];
        const result = this.hash(input, traces);

        const proofStream = new ProofStream([]);
        const stark = new Stark(this.field, this.byteLength, this.expansionFactor, this.securityLevel, 2, this.rounds, Number(this.alpha), this.fieldGenerator);

        const transitionConstraints = this.getTransitionConstraints(stark.omicronDomain, this.field);

        const boundaryConditions: BoundaryConditions = new Map([
            [0, [{cycle: this.rounds-1, value: result}]],
            [1, [{cycle: 0, value: 0n}]]
        ]);

        stark.prove(traces, transitionConstraints, boundaryConditions, proofStream, runChecks);

        return {
            proof: proofStream,
            output: result
        }

    }

}