import {FiniteField, Polynom} from "@guildofweavers/galois";
import {Polynomial} from "./Polynomial";


export class MultiPolynomial {

    field: FiniteField;
    coefficients: Map<bigint[], bigint>;
    numVariables: number;

    constructor(coefficients: Map<bigint[], bigint>, field: FiniteField) {
        this.field = field;

        let max = 0;
        coefficients.forEach((value, key) => {
            if(value===0n) return;
            max = Math.max(key.length, max);
        });
        this.numVariables = max;

        this.coefficients = coefficients;
    }

    static zero(field: FiniteField): MultiPolynomial {
        return new MultiPolynomial(new Map(), field);
    }

    add(b: MultiPolynomial): MultiPolynomial {

        const numVariables = Math.max(this.numVariables, b.numVariables);
        const coefficients = new Map<bigint[], bigint>();

        this.coefficients.forEach((value, key) => {
            const padded = key.concat(new Array<bigint>(numVariables-key.length).fill(0n));
            coefficients.set(padded, value);
        });

        b.coefficients.forEach((value, key) => {
            const padded = key.concat(new Array<bigint>(numVariables-key.length).fill(0n));
            const coefficient = coefficients.get(padded);
            if(coefficient==null) {
                coefficients.set(padded, value);
            } else {
                coefficients.set(padded, this.field.add(coefficient, value));
            }
        });

        return new MultiPolynomial(coefficients, this.field);

    }

    mulByConstant(b: bigint) {

        const coefficients = new Map<bigint[], bigint>();
        for(let val of this.coefficients.entries()) {
            coefficients.set(val[0], this.field.mul(val[1], b));
        }

        return new MultiPolynomial(coefficients, this.field);

    }

    mul(b: MultiPolynomial): MultiPolynomial {

        const numVariables = this.numVariables+b.numVariables;
        const coefficients = new Map<bigint[], bigint>();

        this.coefficients.forEach((v0, k0) => {
            b.coefficients.forEach((v1, k1) => {
                const exponent = new Array<bigint>(numVariables);
                exponent[numVariables-1] = 0n;
                exponent.fill(0n, 0, numVariables);
                k0.forEach((value, index) => {
                    exponent[index] = this.field.add(exponent[index], value);
                });
                k1.forEach((value, index) => {
                    exponent[index] = this.field.add(exponent[index], value);
                });
                const prevExp = coefficients.get(exponent);
                if(prevExp==null) {
                    coefficients.set(exponent, this.field.mul(v0, v1));
                } else {
                    coefficients.set(exponent, this.field.add(
                        prevExp,
                        this.field.mul(v0, v1)
                    ));
                }
            });
        });

        return new MultiPolynomial(coefficients, this.field);

    }

    sub(b: MultiPolynomial): MultiPolynomial {

        const numVariables = Math.max(this.numVariables, b.numVariables);
        const coefficients = new Map<bigint[], bigint>();

        this.coefficients.forEach((value, key) => {
            const padded = key.concat(new Array<bigint>(numVariables-key.length).fill(0n));
            coefficients.set(padded, value);
        });

        b.coefficients.forEach((value, key) => {
            const padded = key.concat(new Array<bigint>(numVariables-key.length).fill(0n));
            const coefficient = coefficients.get(padded);
            if(coefficient==null) {
                coefficients.set(padded, this.field.neg(value));
            } else {
                coefficients.set(padded, this.field.sub(coefficient, value));
            }
        });

        return new MultiPolynomial(coefficients, this.field);

    }

    power(b: bigint): MultiPolynomial {

        if(b===0n) return MultiPolynomial.constant(1n, this.field);
        let acc = new MultiPolynomial(new Map<bigint[], bigint>([
            [Array<bigint>(this.numVariables).fill(0n), 1n]
        ]), this.field);

        const bitLength = b.toString(2).length;
        for(let i=bitLength-1;i--;i>=0) {
            acc = acc.mul(acc);
            if(((b>>BigInt(i)) & 1n) === 1n) {
                acc = acc.mul(this);
            }
        }

        return acc;

    }

    isZero(): boolean {
        for(let entry of this.coefficients.entries()) {
            if(entry[1]!==0n) return false;
        }
        return true;
    }

    evaluate(point: bigint[]): bigint {
        let acc: bigint = 0n;

        const powerMap: bigint[][] = [];

        this.coefficients.forEach((value, key) => {
            for(let i=0;i<key.length;i++) {
                if(key[i]!==0n) {
                    let power: bigint;
                    if(powerMap[i]!=null) {
                        power = powerMap[i][Number(key[i])]
                    } else {
                        powerMap[i] = [];
                    }
                    if(power==null) {
                        power = this.field.exp(point[i], key[i]);
                        powerMap[i][Number(key[i])] = power;
                    }
                    value = this.field.mul(
                        value,
                        power
                    );
                }
            }

            acc = this.field.add(acc, value);
        });

        return acc;
    }

    _evaluateSymbolic(point: Polynomial[]): Polynomial {

        let acc: Polynom = null;

        this.coefficients.forEach((value, key) => {

            let resultPoly: Polynom = this.field.newVectorFrom([value]);

            for(let i=0;i<key.length;i++) {
                if(key[i]!==0n) {
                    if(key[i]!==0n) resultPoly = this.field.mulPolys(resultPoly, point[i].power(key[i]).coefficients);
                }
            }

            if(acc==null) {
                acc = resultPoly;
            } else {
                acc = this.field.addPolys(acc, resultPoly);
            }

        });

        return new Polynomial(acc, this.field);

    }

    evaluateSymbolic(point: Polynomial[]): Polynomial {

        let acc: Polynom;

        const polyPowers: Polynomial[][] = [];

        this.coefficients.forEach((value, key) => {

            let resultPoly: Polynom;

            for(let i=0;i<key.length;i++) {
                if(key[i]!==0n) {
                    if(polyPowers[i]==null) polyPowers[i] = [];
                    let expPoly = polyPowers[i][Number(key[i])];
                    if(expPoly==null) {
                        expPoly = point[i].power(key[i]);
                        polyPowers[i][Number(key[i])] = expPoly;
                    }

                    if(resultPoly==null) {
                        resultPoly = expPoly.coefficients;
                    } else {
                        resultPoly = this.field.mulPolys(resultPoly, expPoly.coefficients);
                    }
                }
            }

            if(resultPoly==null) return;

            resultPoly = this.field.mulPolyByConstant(resultPoly, value);

            if(acc==null) {
                acc = resultPoly;
            } else {
                acc = this.field.addPolys(acc, resultPoly);
            }

        });

        return new Polynomial(acc, this.field);

    }

    static constant(value: bigint, field: FiniteField): MultiPolynomial {
        return new MultiPolynomial(new Map<bigint[], bigint>([
            [[0n], value]
        ]), field);
    }

    static lift(poly: Polynomial, variableIndex: number): MultiPolynomial {
        const mCoefficients: [bigint[], bigint][] = [];
        const arr = Array(variableIndex);
        arr[variableIndex-1] = 0n;
        arr.fill(0n, 0, variableIndex);
        for(let i=0;i<poly.coefficients.length;i++) {
            mCoefficients.push([
                arr.concat([BigInt(i)]),
                poly.coefficients.getValue(i)
            ]);
        }
        return new MultiPolynomial(new Map<bigint[], bigint>(mCoefficients), poly.field);
    }

}