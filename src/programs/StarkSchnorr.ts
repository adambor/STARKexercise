import {BoundaryConditions, Stark} from "../Stark";
import {FiniteField} from "@guildofweavers/galois";
import {ProofStream} from "../fiatshamir/ProofStream";
import {MultiPolynomial} from "../polynomial/MultiPolynomial";
import {FastStark} from "../FastStark";
import {Polynomial} from "../polynomial/Polynomial";
import {randomBytes} from "crypto";


/*
Inputs:
 - R (2 felts) - signature nonce
 - s (1 felt) - signature s value
 - e (1 felt) - message hash
 - P (2 felts) - public key
*/

/*
Pn = -P

H = R + eP
S = sG

Registers:
    [0] e bits
    [1] e sum

    [2] Hx
    [3] Hy

    [4] Pnx
    [5] Pny
    [6] Pn double lambda: lambda*2Pny = 3Pnx^2 + a
    [7] Pn + H sum lambda: (Pnx - Hx)*lambda = (Pny - Hy)

    [8] s bits
    [9] s sum

    [10] Sx
    [11] Sy

    [12] S sum lambda: (iGx - Sx)*lambda = (iGy - Sy)
*/

/*
Start constraints:
    - H = R
End constraints:
    - s sum = s
    - e sum = e
 */

/*
num1 > num2:
enableFlag: starts at 1
if enableFlag then bitNum1 - bitNum2 = 1/0
if enableFlag then enableFlag = enableFlag - (bitNum1 - bitNum2)
 */

//Requires the use of Starkware field: 2n ** 251n + 17n * 2n ** 192n + 1n

const totalRegisters = 8;

let createdRegisters = 0;
function createRegister(): [number, number] {
    const arr: [number, number] = [1+createdRegisters, 1+createdRegisters+totalRegisters];
    createdRegisters++;
    return arr;
}

function toRow(...variables: [number, bigint][]): bigint[] {
    const array: bigint[] = Array(totalRegisters*2 + 1);
    array[totalRegisters*2] = 0n;
    array.fill(0n, 0, totalRegisters*2 + 1);

    for(let v of variables) {
        array[v[0]] = v[1];
    }

    return array;
}

const eBits = createRegister();
const eSum = createRegister();
const Hx = createRegister();
const Hy = createRegister();
const Pnx = createRegister();
const Pny = createRegister();
const lambdaPnDouble = createRegister();
const lambdaHSum = createRegister();

const groupOrder = 3618502788666131213697322783095070105526743751716087489154079457884512865583n;
export const generatorPoint: [bigint, bigint] = [874739451078007766457464989774322083649278607533249481151382481072868806602n, 152666792071518830868575557812948353041420400780739481342941381225525861407n];
const alpha = 1n;
const beta = 3141592653589793238462643383279502884197169399375105820974944592307816406665n;

const fieldBits = 255;

const TRANSITION_CONSTRAINTS = [
    new Map<bigint[], bigint>([
        [toRow([eBits[0], 2n]), 1n],
        [toRow([eBits[0], 1n]), -1n]
    ]), //Constaint bits (e bits) to 0 or 1 => (x0-1)x0 = x0^2 - x0

    new Map<bigint[], bigint>([
        [toRow([lambdaPnDouble[0], 1n], [Pny[0], 1n]), 2n],
        [toRow([Pnx[0], 2n]), -3n],
        [toRow(), (-1n)*alpha]
    ]), //Public key doubling lambda: 2*lambda*Pny = 3Pnx^2 + a
    new Map<bigint[], bigint>([
        [toRow([Pnx[1], 1n]), 1n],
        [toRow([lambdaPnDouble[0], 2n]), -1n],
        [toRow([Pnx[0], 1n]), 2n],
    ]), //Public key doubling: P1nx = lambda^2 - 2*P0nx
    new Map<bigint[], bigint>([
        [toRow([Pny[1], 1n]), 1n],
        [toRow([lambdaPnDouble[0], 1n], [Pnx[0], 1n]), -1n],
        [toRow([lambdaPnDouble[0], 1n], [Pnx[1], 1n]), 1n],
        [toRow([Pny[0], 1n]), 1n],
    ]), //Public key doubling: P1ny = lambda*(P0nx - P1nx) - P0ny

    new Map<bigint[], bigint>([
        [toRow([lambdaHSum[0], 1n], [Pnx[0], 1n]), 1n],
        [toRow([lambdaHSum[0], 1n], [Hx[0], 1n]), -1n],
        [toRow([Pny[0], 1n]), -1n],
        [toRow([Hy[0], 1n]), 1n],
    ]), //Pn + H sum lambda: (Pnx - Hx)*lambda = (Pny - Hy)

    //Pn + H point add if e is 1
    new Map<bigint[], bigint>([
        [toRow([eBits[0], 1n], [Hx[1], 1n]), 1n],
        [toRow([eBits[0], 1n], [lambdaHSum[0], 2n]), -1n],
        [toRow([eBits[0], 1n], [Hx[0], 1n]), 1n],
        [toRow([eBits[0], 1n], [Pnx[0], 1n]), 1n],
    ]),
    //x coordinate:
    // (H1x = lambda^2 - H0x - P0nx)*e
    // (H1x - lambda^2 + H0x + P0nx)*e
    // e*H1x - e*lambda^2 + e*H0x + e*P0nx

    new Map<bigint[], bigint>([
        [toRow([eBits[0], 1n], [Hy[1], 1n]), 1n],
        [toRow([eBits[0], 1n], [lambdaHSum[0], 1n], [Hx[0], 1n]), -1n],
        [toRow([eBits[0], 1n], [lambdaHSum[0], 1n], [Hx[1], 1n]), 1n],
        [toRow([eBits[0], 1n], [Hy[0], 1n]), 1n],
    ]),
    //y coordinate:
    // (H1y = lambda*(H0x - H1x) - H0y)*e
    // (H1y - lambda*(H0x - H1x) + H0y)*e
    // (H1y - lambda*H0x + lambda*H1x + H0y)*e
    // e*H1y - e*lambda*H0x + e*lambda*H1x + e*H0y

    //H0 = H1 if e is 0
    new Map<bigint[], bigint>([
        [toRow([Hx[1], 1n]), 1n],
        [toRow([Hx[0], 1n]), -1n],
        [toRow([eBits[0], 1n], [Hx[1], 1n]), -1n],
        [toRow([eBits[0], 1n], [Hx[0], 1n]), 1n],
    ]),
    //x coordinate:
    // (H1x = H0x)*(1-e)
    // (H1x - H0x)*(1-e)
    // (H1x - H0x) - e*(H1x - H0x)
    // H1x - H0x - e*H1x + e*H0x

    new Map<bigint[], bigint>([
        [toRow([Hy[1], 1n]), 1n],
        [toRow([Hy[0], 1n]), -1n],
        [toRow([eBits[0], 1n], [Hy[1], 1n]), -1n],
        [toRow([eBits[0], 1n], [Hy[0], 1n]), 1n],
    ]),
    //y coordinate:
    // (H1y = H0y)*(1-e)
    // (H1y - H0y)*(1-e)
    // (H1y - H0y) - e*(H1y - H0y)
    // H1y - H0y - e*H1y + e*H0y

];

export class StarkSchnorr {

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

    ecDouble(point: [bigint, bigint]): [bigint, bigint] {
        const lambda = this.field.div(
            this.field.add(
                this.field.mul(3n, this.field.exp(point[0], 2n)),
                alpha
            ),
            this.field.mul(2n, point[1])
        );
        const _X = this.field.sub(
            this.field.exp(lambda, 2n),
            this.field.mul(2n, point[0])
        );
        return [
            _X,
            this.field.sub(
                this.field.mul(
                    lambda,
                    this.field.sub(point[0], _X)
                ),
                point[1]
            )
        ];
    }

    ecAdd(point1: [bigint, bigint], point2: [bigint, bigint]): [bigint, bigint] {
        if(point1[0]===point2[0] && point1[1]===point2[1]) return this.ecDouble(point1);

        const lambda = this.field.div(
            this.field.sub(point2[1], point1[1]),
            this.field.sub(point2[0], point1[0])
        );
        const _X = this.field.sub(
            this.field.exp(lambda, 2n),
            this.field.add(point1[0], point2[0])
        );
        return [
            _X,
            this.field.sub(
                this.field.mul(
                    lambda,
                    this.field.sub(point1[0], _X)
                ),
                point1[1]
            )
        ];
    }

    ecMul(scalar: bigint, point: [bigint, bigint]): [bigint, bigint] {

        let accumulator: [bigint, bigint] = null;

        for(let i=fieldBits;i>=0;i--) {
            //Double
            if(accumulator!=null) {
                accumulator = this.ecDouble(accumulator);
            }

            //Add
            const bit = (scalar>>BigInt(i)) & 1n;
            if(bit===1n) {
                if(accumulator==null) {
                    accumulator = point;
                } else {
                    accumulator = this.ecAdd(accumulator, point);
                }
            }
        }

        return accumulator;

    }

    randomKey(): bigint {
        return this.field.prng(randomBytes(32));
    }

    toPublicKey(privateKey: bigint): [bigint, bigint] {
        return this.ecMul(privateKey, generatorPoint);
    }

    sign(privateKey: bigint, e: bigint): {R: [bigint, bigint], s: bigint} {
        const k = this.field.prng(randomBytes(32));
        const R = this.ecMul(k, generatorPoint);
        const s = (k + (e*privateKey)) % groupOrder;

        return {
            R,
            s
        };
    }

    sigVerify(publicKey: [bigint, bigint], e: bigint, signature: {R: [bigint, bigint], s: bigint}): boolean {
        const left = this.ecAdd(signature.R, this.ecMul(e, publicKey));
        const right = this.ecMul(signature.s, generatorPoint);

        console.log(left);
        console.log(right);

        return left[0]===right[0] && left[1]===right[1];
    }

    prove(nonceR: [bigint, bigint], hashe: bigint, pubkeyP: [bigint, bigint], runChecks?: boolean): {
        proof: ProofStream
    } {

        const stark = new FastStark(this.field, this.byteLength, this.expansionFactor, this.securityLevel, totalRegisters, fieldBits+1, 3, this.fieldGenerator, this.foldingFactor);

        console.log("Unexpanded omicron len: ", stark.unexpandedOmicronDomain.length);
        console.log("Omicron len: ", stark.omicronDomain.length);
        console.log("Omega len: ", stark.omegaDomain.length);
        console.log("Unexpanded omicron: ", stark.unexpandedOmicron);
        console.log("Omicron^omicron expansion: ", this.field.exp(stark.omicron, BigInt(stark.omicronExpansionFactor)));

        const powersOf2 =this.field.getPowerSeries(2n, fieldBits+1).toValues();

        const powersOf2Poly = Polynomial.interpolateDomain(stark.unexpandedOmicronDomain, powersOf2, this.field);

        //Create summand for num 1
        const num1Summand = new MultiPolynomial(new Map<bigint[], bigint>([
            [toRow([eSum[0], 1n]), 1n],
            [toRow([eSum[1], 1n]), -1n],
        ]), this.field).add(
            MultiPolynomial.lift(powersOf2Poly, 0).mul(
                MultiPolynomial.lift(new Polynomial(this.field.newVectorFrom([0n, 1n]), this.field), eBits[0])
            )
        ); //Summand for num 1

        const transitionConstraints = TRANSITION_CONSTRAINTS
            .map(data => new MultiPolynomial(data, this.field))
            .concat(num1Summand);

        const num1Binary = hashe.toString(2).padStart(fieldBits+1, "0").split("").reverse().join("");

        const traces: bigint[][] = Array<bigint[]>(totalRegisters);
        for(let i=0;i<totalRegisters;i++) {
            traces[i] = [];
        }

        let sum: bigint = 0n;
        let H: [bigint, bigint] = nonceR;
        let Pn: [bigint, bigint] = pubkeyP;

        for(let i=0;i<fieldBits+1;i++) {
            //Bit decomposition
            const bit1 = BigInt(num1Binary.charAt(i));
            traces[eBits[0]-1].push(bit1);
            const bit1Mul = this.field.mul(bit1, powersOf2[i]);
            traces[eSum[0]-1].push(sum);
            sum = this.field.add(sum, bit1Mul);

            traces[Hx[0]-1].push(H[0]);
            traces[Hy[0]-1].push(H[1]);

            traces[Pnx[0]-1].push(Pn[0]);
            traces[Pny[0]-1].push(Pn[1]);

            const _lambdaPnDouble = this.field.div(
                this.field.add(
                    this.field.mul(3n, this.field.exp(Pn[0], 2n)),
                    alpha
                ),
                this.field.mul(2n, Pn[1])
            );
            traces[lambdaPnDouble[0]-1].push(_lambdaPnDouble);

            const _lambdaHSum = this.field.div(
                this.field.sub(Pn[1], H[1]),
                this.field.sub(Pn[0], H[0])
            );
            traces[lambdaHSum[0]-1].push(_lambdaHSum);

            if(bit1===1n) {
                const _Hx = this.field.sub(
                    this.field.exp(_lambdaHSum, 2n),
                    this.field.add(H[0], Pn[0])
                );
                H = [
                    _Hx,
                    this.field.sub(
                        this.field.mul(
                            _lambdaHSum,
                            this.field.sub(H[0], _Hx)
                        ),
                        H[1]
                    )
                ];
            }

            const _Pnx = this.field.sub(
                this.field.exp(_lambdaPnDouble, 2n),
                this.field.mul(2n, Pn[0])
            );
            Pn = [
                _Pnx,
                this.field.sub(
                    this.field.mul(
                        _lambdaPnDouble,
                        this.field.sub(Pn[0], _Pnx)
                    ),
                    Pn[1]
                )
            ];
        }

        // for(let i=0;i<fieldBits;i++) {
        //     const x = stark.unexpandedOmicronDomain[i];
        //
        //     let _traces = Array<bigint>(totalRegisters);
        //     let _tracesPlus1 = Array<bigint>(totalRegisters);
        //     for(let e=0;e<totalRegisters;e++) {
        //         _traces[e] = traces[e][i];
        //         _tracesPlus1[e] = traces[e][i+1];
        //     }
        //
        //     const state = [x].concat(_traces, _tracesPlus1);
        //
        //     const evaluations = transitionConstraints.map(poly => poly.evaluate(state));
        //
        //     console.log(evaluations);
        // }

        console.log(traces[Hx[0]-1][255]);
        console.log(traces[Hy[0]-1][255]);

        const boundaryConditions: BoundaryConditions = new Map([
            [eBits[0]-1, [{cycle: fieldBits, value: 0n}]],
            [eSum[0]-1, [{cycle: 0, value: 0n}, {cycle: fieldBits, value: hashe}]],
            [Hx[0]-1, [{cycle: 0, value: nonceR[0]}]],
            [Hy[0]-1, [{cycle: 0, value: nonceR[1]}]],
            [Pnx[0]-1, [{cycle: 0, value: pubkeyP[0]}]],
            [Pny[0]-1, [{cycle: 0, value: pubkeyP[1]}]]
        ]);

        const proofStream = new ProofStream([]);
        stark.prove(traces, transitionConstraints, boundaryConditions, proofStream, runChecks);

        return {
            proof: proofStream
        };

    }

    verify(nonceR: [bigint, bigint], hashe: bigint, pubkeyP: [bigint, bigint], proof: ProofStream) {

        const stark = new FastStark(this.field, this.byteLength, this.expansionFactor, this.securityLevel, totalRegisters, fieldBits+1, 3, this.fieldGenerator, this.foldingFactor);

        console.log("Unexpanded omicron len: ", stark.unexpandedOmicronDomain.length);
        console.log("Omicron len: ", stark.omicronDomain.length);
        console.log("Omega len: ", stark.omegaDomain.length);
        console.log("Unexpanded omicron: ", stark.unexpandedOmicron);
        console.log("Omicron^omicron expansion: ", this.field.exp(stark.omicron, BigInt(stark.omicronExpansionFactor)));

        const powersOf2 =this.field.getPowerSeries(2n, fieldBits+1).toValues();

        const powersOf2Poly = Polynomial.interpolateDomain(stark.unexpandedOmicronDomain, powersOf2, this.field);

        //Create summand for num 1
        const num1Summand = new MultiPolynomial(new Map<bigint[], bigint>([
            [toRow([eSum[0], 1n]), 1n],
            [toRow([eSum[1], 1n]), -1n],
        ]), this.field).add(
            MultiPolynomial.lift(powersOf2Poly, 0).mul(
                MultiPolynomial.lift(new Polynomial(this.field.newVectorFrom([0n, 1n]), this.field), eBits[0])
            )
        ); //Summand for num 1

        const transitionConstraints = TRANSITION_CONSTRAINTS
            .map(data => new MultiPolynomial(data, this.field))
            .concat(num1Summand);

        const boundaryConditions: BoundaryConditions = new Map([
            [eBits[0]-1, [{cycle: fieldBits, value: 0n}]],
            [eSum[0]-1, [{cycle: 0, value: 0n}, {cycle: fieldBits, value: hashe}]],
            [Hx[0]-1, [{cycle: 0, value: nonceR[0]}]],
            [Hy[0]-1, [{cycle: 0, value: nonceR[1]}]],
            [Pnx[0]-1, [{cycle: 0, value: pubkeyP[0]}]],
            [Pny[0]-1, [{cycle: 0, value: pubkeyP[1]}]]
        ]);

        stark.verify(proof, transitionConstraints, boundaryConditions);
    }

}