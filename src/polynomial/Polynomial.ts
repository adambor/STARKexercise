import {FiniteField, Polynom, Vector} from "@guildofweavers/galois";

function getNearestPowerOf2(degree: number) {
    let i = 1;
    while(i<degree+1) {
        i *= 2;
    }
    return i;
}

export class Polynomial {

    field: FiniteField;
    coefficients: Vector;

    constructor(coefficients: Vector, field: FiniteField) {
        this.field = field;
        this.coefficients = coefficients;
    }

    degree(): number {
        for(let i=this.coefficients.length-1;i>=0;i--) {
            if(this.coefficients.getValue(i)>0n) return i;
        }
        return -1;
    }

    add(b: Polynomial): Polynomial {
        return new Polynomial(this.field.addPolys(this.coefficients, b.coefficients), this.field);
    }

    sub(b: Polynomial): Polynomial {
        return new Polynomial(this.field.subPolys(this.coefficients, b.coefficients), this.field);
    }

    fastMul(b: Polynomial): Polynomial {

        const degree1 = this.degree();
        const degree2 = b.degree();

        const degreeSum = degree1 + degree2;

        if(degreeSum<8) {
            return this.mul(b);
        }

        const evaluationDomain = getNearestPowerOf2(degreeSum);

        const omega = this.field.getRootOfUnity(evaluationDomain);
        const powersOfOmega = this.field.getPowerSeries(omega, evaluationDomain);

        const codeword1 = this.field.evalPolyAtRoots(this.coefficients, powersOfOmega).toValues();
        const codeword2 = this.field.evalPolyAtRoots(b.coefficients, powersOfOmega).toValues();

        const resultCodeword = codeword1.map((value, index) => {
            return this.field.mul(value, codeword2[index]);
        });

        return Polynomial.interpolateAtRoots(powersOfOmega.toValues(), resultCodeword, this.field);

    }

    mul(b: Polynomial): Polynomial {
        return new Polynomial(this.field.mulPolys(this.coefficients, b.coefficients), this.field);
    }

    equals(b: Polynomial): boolean {
        for(let i=0;i<this.coefficients.length;i++) {
            if(this.coefficients.getValue(i)!==b.coefficients.getValue(i)) return false;
        }
        return true;
    }

    isZero(): boolean {
        return this.degree()===-1;
    }

    leadingCoefficient(): bigint {
        for(let i=this.coefficients.length-1;i>=0;i--) {
            if(this.coefficients.getValue(i)>0n) return this.coefficients.getValue(i);
        }
        return null;
    }

    /*
        def divide( numerator, denominator ):
        if denominator.degree() == -1:
            return None
        if numerator.degree() < denominator.degree():
            return (Polynomial([]), numerator)
        field = denominator.coefficients[0].field
        remainder = Polynomial([n for n in numerator.coefficients])
        quotient_coefficients = [field.zero() for i in range(numerator.degree()-denominator.degree()+1)]
        for i in range(numerator.degree()-denominator.degree()+1):
            if remainder.degree() < denominator.degree():
                break
            coefficient = remainder.leading_coefficient() / denominator.leading_coefficient()
            shift = remainder.degree() - denominator.degree()
            subtractee = Polynomial([field.zero()] * shift + [coefficient]) * denominator
            quotient_coefficients[shift] = coefficient
            remainder = remainder - subtractee
        quotient = Polynomial(quotient_coefficients)
        return quotient, remainder
     */

    divide(b: Polynomial): Polynomial {
        return new Polynomial(this.field.divPolys(this.coefficients, b.coefficients), this.field);
    }

    scale(b: bigint): Polynomial {
        let currPower = 1n;
        const scaledCoefficients = this.coefficients.toValues().map(val => {
            let result = this.field.mul(
                val,
                currPower
            );
            currPower = this.field.mul(currPower, b);
            return result;
        });
        return new Polynomial(this.field.newVectorFrom(scaledCoefficients), this.field);
    }

    power(b: bigint): Polynomial {
        if(b===0n) return new Polynomial(this.field.newVectorFrom([1n]), this.field);
        let acc = this.field.newVectorFrom([1n]);

        const bitLength = b.toString(2).length;
        for(let i=bitLength-1;i--;i>=0) {
            acc = this.field.mulPolys(acc, acc);
            if(((b>>BigInt(i)) & 1n) === 1n) {
                acc = this.field.mulPolys(acc, this.coefficients);
            }
        }

        return new Polynomial(acc, this.field);
    }

    evaluate(point: bigint): bigint {
        return this.field.evalPolyAt(this.coefficients, point);
    }

    evaluateDomain(points: bigint[]): bigint[] {
        return points.map(point => this.field.evalPolyAt(this.coefficients, point));
    }

    evaluateAtRoots(points: bigint[]): bigint[] {
        return this.field.evalPolyAtRoots(this.coefficients, this.field.newVectorFrom(points)).toValues();
    }

    evaluateAtRootsWithOffset(points: bigint[], offset: bigint): bigint[] {
        let currPower = 1n;
        const scaledCoefficients = this.coefficients.toValues().map(val => {
            let result = this.field.mul(
                val,
                currPower
            );
            currPower = this.field.mul(currPower, offset);
            return result;
        });
        return this.field.evalPolyAtRoots(this.field.newVectorFrom(scaledCoefficients), this.field.newVectorFrom(points)).toValues();
    }

    static interpolateDomain(domain: bigint[], values: bigint[], field: FiniteField): Polynomial {
        return new Polynomial(field.interpolate(field.newVectorFrom(domain), field.newVectorFrom(values)), field);
    }

    static interpolateAtRoots(domain: bigint[], values: bigint[], field: FiniteField): Polynomial {
        return new Polynomial(field.interpolateRoots(field.newVectorFrom(domain), field.newVectorFrom(values)), field);
    }

    static interpolateAtRootsWithOffset(domain: bigint[], values: bigint[], offset: bigint, field: FiniteField): Polynomial {
        const offsetInv = field.inv(offset);

        const originalCoefficients = field.interpolateRoots(field.newVectorFrom(domain), field.newVectorFrom(values)).toValues();
        let currPower = 1n;
        originalCoefficients.forEach((val, index) => {
            let result = field.mul(
                val,
                currPower
            );
            currPower = field.mul(currPower, offsetInv);
            originalCoefficients[index] = result;
        });

        return new Polynomial(field.newVectorFrom(originalCoefficients), field);
    }

    static zerofier(domain: bigint[], field: FiniteField): Polynomial {

        const x = field.newVectorFrom([0n, 1n]);
        let acc = field.newVectorFrom([1n]);
        for(let d of domain) {
            acc = field.mulPolys(
                acc,
                field.subPolys(x, field.newVectorFrom([d]))
            );
        }

        return new Polynomial(acc, field);

    }

    static fastZerofier(domain: bigint[], field: FiniteField) {

        if(domain.length<=256) return Polynomial.zerofier(domain, field);

        let degree = 4;
        let lastLayer: Polynom[] = [];

        //console.time("Polynomial.fastZerofier: Pre-process");
        for(let i=0;i<Math.ceil(domain.length/degree);i++) {
            if((degree*i)+3<domain.length) {
                const a = domain[degree*i];
                const b = domain[degree*i + 1];
                const c = domain[degree*i + 2];
                const d = domain[degree*i + 3];
                lastLayer[i] = field.newVectorFrom([
                    field.mul(field.mul(a, b), field.mul(c, d)),
                    field.neg(field.add(
                        field.add(
                            field.mul(a, field.mul(b, c)),
                            field.mul(a, field.mul(b, d))
                        ),
                        field.add(
                            field.mul(a, field.mul(c, d)),
                            field.mul(b, field.mul(c, d))
                        )
                    )),
                    field.add(
                        field.add(
                            field.mul(a, b),
                            field.mul(a, c)
                        ),
                        field.add(
                            field.add(
                                field.mul(a, d),
                                field.mul(b, c)
                            ),
                            field.add(
                                field.mul(b, d),
                                field.mul(c, d)
                            )
                        )
                    ),
                    field.neg(field.add(field.add(a, b), field.add(c, d))),
                    1n
                ]);

            } else if((degree*i)+2<domain.length) {
                const a = domain[degree*i];
                const b = domain[degree*i + 1];
                const c = domain[degree*i + 2];
                lastLayer[i] = field.newVectorFrom([
                    field.neg(field.mul(a, field.mul(b, c))),
                    field.add(
                        field.mul(a,b),
                        field.add(
                            field.mul(b,c),
                            field.mul(c,a)
                        )
                    ),
                    field.neg(field.add(a, field.add(b, c))),
                    1n
                ]);
            } else if((degree*i)+1<domain.length) {
                const a = domain[degree*i];
                const b = domain[degree*i + 1];
                lastLayer[i] = field.newVectorFrom([field.mul(a, b), field.neg(field.add(a, b)), 1n]);
            } else {
                lastLayer[i] = field.newVectorFrom([field.neg(domain[degree*i]), 1n]);
            }
        }
        // console.timeEnd("Polynomial.fastZerofier: Pre-process");

        while(lastLayer.length>1) {
            const newLayer: Polynom[] = [];
            for(let i=0;i<Math.ceil(lastLayer.length/2);i++) {
                if(lastLayer[(2*i) + 1]==null) {
                    newLayer[i] = lastLayer[2*i];
                } else {
                    newLayer[i] = Polynomial.fastMulPolynom(
                        lastLayer[2*i],
                        lastLayer[(2*i) + 1],
                        field,
                        degree*4
                    );
                }
            }
            lastLayer = newLayer;
            degree *= 2;
        }

        return new Polynomial(lastLayer[0], field);

    }

    static testColinearity(points: bigint[][], field: FiniteField) {
        const domain = points.map(val => val[0]);
        const values = points.map(val => val[1]);
        const polynomial = field.interpolate(field.newVectorFrom(domain), field.newVectorFrom(values));

        for(let i=polynomial.length;i--;i>=0) {
            if(polynomial.getValue(i)>0n) {
                return i<=1;
            }
        }

        return true;
    }

    static fastMulPolynom(a: Polynom, b: Polynom, field: FiniteField, evaluationDomain: number) {

        if(evaluationDomain<=256) return field.mulPolys(a, b);

        // console.time("Polynomial.fastMulPolynom: Roots of unity");
        const omega = field.getRootOfUnity(evaluationDomain);
        const powersOfOmega = field.getPowerSeries(omega, evaluationDomain);
        // console.timeEnd("Polynomial.fastMulPolynom: Roots of unity");

        // console.time("Polynomial.fastMulPolynom: Eval polys");
        const codeword1 = field.evalPolyAtRoots(a, powersOfOmega).toValues();
        const codeword2 = field.evalPolyAtRoots(b, powersOfOmega).toValues();
        // console.timeEnd("Polynomial.fastMulPolynom: Eval polys");

        // console.time("Polynomial.fastMulPolynom: Result codeword");
        const resultCodeword = codeword1.map((value, index) => {
            return field.mul(value, codeword2[index]);
        });
        // console.timeEnd("Polynomial.fastMulPolynom: Result codeword");

        // console.time("Polynomial.fastMulPolynom: Interpolate");
        const result = field.interpolateRoots(powersOfOmega, field.newVectorFrom(resultCodeword));
        // console.timeEnd("Polynomial.fastMulPolynom: Interpolate");

        return result;

    }

}