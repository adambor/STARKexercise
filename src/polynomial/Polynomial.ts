import {FiniteField, Polynom, Vector} from "@guildofweavers/galois";

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
            )
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

    static interpolateDomain(domain: bigint[], values: bigint[], field: FiniteField): Polynomial {
        return new Polynomial(field.interpolate(field.newVectorFrom(domain), field.newVectorFrom(values)), field);
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



}