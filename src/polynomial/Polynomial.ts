import {FiniteField, Polynom, Vector} from "@guildofweavers/galois";

export function getNanos(): number {
    const hrTime = process.hrtime();

    return hrTime[0] * 1000000000 + hrTime[1];
}

function getNearestPowerOf2(degree: number) {
    let i = 1;
    while(i<degree+1) {
        i *= 2;
    }
    return i;
}

type ZerofierCache = {
    even?: {
        poly?: Polynom,
        children?: ZerofierCache
    },
    odd?: {
        poly?: Polynom,
        children?: ZerofierCache
    },
};

export class Polynomial {

    field: FiniteField;
    coefficients: Vector;

    constructor(coefficients: Vector, field: FiniteField) {
        this.field = field;
        this.coefficients = coefficients;
    }

    degree(): number {
        for(let i=this.coefficients.length-1;i>=0;i--) {
            if(this.coefficients.getValue(i)!==0n) return i;
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

    mulByConstant(b: bigint): Polynomial {
        return new Polynomial(this.field.mulPolyByConstant(this.coefficients, b), this.field);
    }

    equals(b: Polynomial): boolean {
        for(let i=0;i<this.coefficients.length;i++) {
            if((this.coefficients.getValue(i) || 0n)!==(b.coefficients.getValue(i) || 0n)) {
                return false;
            }
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

    mod(b: Polynomial, times?: number[]): Polynomial {

        if(b.degree()===-1) return null;

        const aDegree = this.degree();
        const bDegree = b.degree();
        if(aDegree<bDegree) return this;

        let remainder: Polynomial = this;
        // const quotientCoefficients = [];
        // quotientCoefficients[aDegree-bDegree] = 0;
        // quotientCoefficients.fill(0n, 0, aDegree-bDegree+1)
        // console.log("Quotient coefficients: ", quotientCoefficients);

        for(let i=0;i<aDegree-bDegree+1;i++) {
            const remDegree = remainder.degree();
            if(remDegree < bDegree) break;

            let startTime = getNanos();
            const coefficient = this.field.div(remainder.leadingCoefficient(), b.leadingCoefficient());
            if(times!=null) times[0] += getNanos()-startTime;
            const shift = remDegree - bDegree;

            // console.log("arr: ", arr);
            // startTime = getNanos();
            // const subtracteeCofficients = []; subtracteeCofficients[shift] = 0n; subtracteeCofficients.fill(0n, 0, shift);
            // for(let i=0;i<b.coefficients.length;i++) {
            //     subtracteeCofficients[i+shift] = b.coefficients.getValue(i) * coefficient;
            // }
            // const subtractee = new Polynomial(this.field.newVectorFrom(subtracteeCofficients), this.field);
            // if(times!=null) times[1] += getNanos()-startTime;

            // quotientCoefficients[shift] = coefficient;
            startTime = getNanos();
            // remainder = remainder.sub(subtractee);
            remainder = new Polynomial(this.field.newVectorFrom(remainder.coefficients.toValues().map((val, index) => {
                if(index<shift || index>=b.coefficients.length+shift) {
                    return val;
                }
                return this.field.sub(val, this.field.mul(b.coefficients.getValue(index-shift), coefficient));
            })), this.field);
            if(times!=null) times[2] += getNanos()-startTime;
        }

        return remainder;

    }

    _mod(b: Polynomial): Polynomial {

        const aValues = this.coefficients.toValues().slice();
        const bValues = b.coefficients.toValues();

        let apos = this.degree();
        let bpos = b.degree();
        if (apos < bpos) {
            throw new Error('Cannot divide by polynomial of higher order');
        }

        let diff = apos - bpos;
        let rValues = new Array<bigint>(diff + 1);

        for (let p = rValues.length - 1; diff >= 0; diff--, apos--, p--) {
            let quot = this.field.div(aValues[apos], bValues[bpos]);
            rValues[p] = quot;
            for (let i = bpos; i >= 0; i--) {
                aValues[diff + i] = this.field.sub(aValues[diff + i], bValues[i] * quot);
            }
        }

        return new Polynomial(this.field.newVectorFrom(aValues), this.field);

    }

    fastDivide(b: Polynomial, offset: bigint): Polynomial {

        const degree1 = this.degree();
        const degree2 = b.degree();

        const degreeSum = Math.max(degree1, degree2);

        if(degreeSum<8) {
            return this.divide(b);
        }

        const evaluationDomain = getNearestPowerOf2(degreeSum);

        const omega = this.field.getRootOfUnity(evaluationDomain);
        const powersOfOmega = this.field.getPowerSeries(omega, evaluationDomain);

        const newVector1 = [];
        const newVector2 = [];

        let currPower = 1n;
        for(let i=0;i<Math.max(this.coefficients.length, b.coefficients.length);i++) {
            if(i<this.coefficients.length) newVector1[i] = this.field.mul(this.coefficients.getValue(i), currPower);
            if(i<b.coefficients.length) newVector2[i] = this.field.mul(b.coefficients.getValue(i), currPower);
            currPower = this.field.mul(currPower, offset);
        }

        const codeword1 = this.field.evalPolyAtRoots(this.field.newVectorFrom(newVector1), powersOfOmega).toValues();
        const codeword2 = this.field.evalPolyAtRoots(this.field.newVectorFrom(newVector2), powersOfOmega).toValues();

        const resultCodeword = codeword1.map((value, index) => {
            return this.field.div(value, codeword2[index]);
        });

        return Polynomial.interpolateAtRootsWithOffset(powersOfOmega.toValues(), resultCodeword, offset, this.field);

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
        for(let i=bitLength-1; i>=0; i--) {
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

    fastEvaluate(point: bigint, poweringMap: bigint[], offset?: number) {

        const mapLength = poweringMap.length;

        let sum = 0n;
        for(let i=0;i<this.coefficients.length;i++) {
            sum = this.field.add(sum, this.field.mul(this.coefficients.getValue(i), poweringMap[(offset*i) % mapLength]));
        }

        return sum;

    }

    evaluateDomainWithPoweringMap(points: bigint[], poweringMap: bigint[]): bigint[] {
        return points.map((point, index) => this.fastEvaluate(point, poweringMap, index));
    }

    evaluateDomain(points: bigint[]): bigint[] {
        return points.map(point => this.field.evalPolyAt(this.coefficients, point));
    }

    fastEvaluateDomain(points: bigint[], offset: bigint, times?: number[]): bigint[] {

        // if(points.length===0) {
        //     return [];
        // } else if(points.length===1) {
        //     return [this.evaluate(points[0])];
        // }

        if(points.length<=1) {
            return this.evaluateDomain(points);
        }

        const half = Math.floor(points.length/2);

        const leftDomain = points.slice(0, half);
        const rightDomain = points.slice(half);

        let startTime = Date.now();
        const leftZerofier = Polynomial.fastZerofier(leftDomain, this.field);
        const rightZerofier = Polynomial.fastZerofier(rightDomain, this.field);
        if(times!=null) times[3] += Date.now() - startTime;

        startTime = Date.now();
        let leftRemainder: Polynomial = this;
        if(leftDomain.length<=this.degree()) {
            // const leftQuotient = this.divide(leftZerofier);
            // leftRemainder = this.sub(leftQuotient.fastMul(leftZerofier));
            leftRemainder = this.mod(leftZerofier, times);
        }

        let rightRemainder: Polynomial = this;
        if(rightDomain.length<=this.degree()) {
            // const rightQuotient = this.divide(rightZerofier);
            // rightRemainder = this.sub(rightQuotient.fastMul(rightZerofier));
            rightRemainder = this.mod(rightZerofier, times);
        }
        if(times!=null) times[4] += Date.now() - startTime;

        //startTime = Date.now();
        const left = leftRemainder.fastEvaluateDomain(leftDomain, offset, times);
        const right = rightRemainder.fastEvaluateDomain(rightDomain, offset, times);
        //if(times!=null) times[2] += Date.now() - startTime;

        return left.concat(right);

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

    static _fastFFTInterpolate(subgroup: bigint[], values: bigint[], field: FiniteField, offset?: number, times?: number[]) {

        if(offset==null) offset = 0;

        if(values.length==0) {
            return new Polynomial(field.newVectorFrom([]), field);
        } else if(values.length==1) {
            return new Polynomial(field.newVectorFrom([values[0]]), field);
        }

        const half = Math.floor(values.length / 2);

        const leftDomain = subgroup.slice(offset, offset+half);
        const rightDomain = subgroup.slice(offset+half, offset+values.length);

        let startTime = Date.now();
        const leftZerofier = Polynomial.fastZerofier(leftDomain, field);
        const rightZerofier = Polynomial.fastZerofier(rightDomain, field);
        if(times!=null) times[0] += Date.now()-startTime;

        startTime = Date.now();
        const leftOffset = rightZerofier.evaluateAtRoots(subgroup).slice(offset, offset+half);
        const rightOffset = leftZerofier.evaluateAtRoots(subgroup).slice(offset+half, offset+values.length);
        if(times!=null) times[1] += Date.now()-startTime;

        const leftInterpolant = Polynomial._fastFFTInterpolate(subgroup, values.slice(0, half).map((val, index) => field.div(val, leftOffset[index])), field, offset, times);
        const rightInterpolant = Polynomial._fastFFTInterpolate(subgroup, values.slice(half).map((val, index) => field.div(val, rightOffset[index])), field, offset+half, times);

        startTime = Date.now();
        const result = leftInterpolant.mul(rightZerofier).add(rightInterpolant.mul(leftZerofier));
        if(times!=null) times[2] += Date.now()-startTime;

        return result;

    }

    static fastMulAndAdd(a: Polynomial, b: Polynomial, c: Polynomial, d: Polynomial, subgroup: bigint[], field: FiniteField): Polynomial {

        const codewordA = a.evaluateAtRoots(subgroup);
        const codewordB = b.evaluateAtRoots(subgroup);
        const codewordC = c.evaluateAtRoots(subgroup);
        const codewordD = d.evaluateAtRoots(subgroup);

        const codewordResult = codewordA.map((_, i) => {
            return field.add(
                field.mul(codewordA[i], codewordB[i]),
                field.mul(codewordC[i], codewordD[i])
            )
        });

        return Polynomial.interpolateAtRoots(subgroup, codewordResult, field);

    }

    static FFT_THRESHOLD = 32;

    static fastFFTInterpolate(subgroup: bigint[], values: bigint[], field: FiniteField, offset?: bigint, times?: number[], cache?: ZerofierCache) {

        // console.log("FTT Interpolate: ", values.length);

        if(offset==null) offset = 1n;

        let startTime = Date.now();
        if(values.length<=Polynomial.FFT_THRESHOLD) {
            const result = Polynomial.interpolateDomain(subgroup.slice(0, values.length).map(val => field.mul(val, offset)), values, field);
            if(times!=null) times[0] += Date.now()-startTime;
            return result;
        }

        startTime = Date.now();
        const omega = subgroup[1];

        const half = Math.ceil(values.length / 2);

        const halfSubgroup = subgroup.filter((val, index) => index%2===0);
        const evenDomain = halfSubgroup.slice(0, half).map(val => field.mul(val, offset));
        const oddDomain = subgroup.filter((val, index) => index%2===1).slice(0, values.length-half).map(val => field.mul(val, offset));
        if(times!=null) times[1] += Date.now()-startTime;

        // console.log("Half subgroup size: ", halfSubgroup.length);

        startTime = Date.now();
        let _evenZerofier: Polynom;
        let _oddZerofier: Polynom;
        if(cache==null || cache.even==null || cache.odd==null) {
            if(cache==null) cache = {};
            cache.odd =  {children: {}};
            cache.even = {children: {}};
            _evenZerofier = Polynomial.fastRecursiveZerofierPolynom(evenDomain, field, halfSubgroup.length, cache.even.children, Polynomial.FFT_THRESHOLD);
            _oddZerofier = Polynomial.fastRecursiveZerofierPolynom(oddDomain, field, halfSubgroup.length, cache.odd.children, Polynomial.FFT_THRESHOLD);
            cache.even.poly = _evenZerofier;
            cache.odd.poly = _oddZerofier;
        } else {
            _evenZerofier = cache.even.poly;
            _oddZerofier = cache.odd.poly;
        }
        const evenZerofier = new Polynomial(_evenZerofier, field);
        const oddZerofier = new Polynomial(_oddZerofier, field);
        if(times!=null) times[2] += Date.now()-startTime;

        // console.log("Even zerofier degree: ", evenZerofier.degree());
        // console.log("Odd zerofier degree: ", oddZerofier.degree());

        startTime = Date.now();
        const evenOffset = oddZerofier.scale(offset).evaluateAtRoots(halfSubgroup).slice(0, half);
        const oddOffset = evenZerofier.scale(field.mul(omega, offset)).evaluateAtRoots(halfSubgroup).slice(0, values.length-half);
        if(times!=null) times[3] += Date.now()-startTime;

        const evenValues = values.filter((_, index) => index%2===0).map((val, index) => field.div(val, evenOffset[index]));
        const oddValues = values.filter((_, index) => index%2===1).map((val, index) => field.div(val, oddOffset[index]));

        const evenInterpolant = Polynomial.fastFFTInterpolate(halfSubgroup, evenValues, field, offset, times, cache.even.children);
        const oddInterpolant = Polynomial.fastFFTInterpolate(halfSubgroup, oddValues, field, field.mul(omega, offset), times, cache.odd.children);

        startTime = Date.now();
        const result = Polynomial.fastMulAndAdd(evenInterpolant, oddZerofier, oddInterpolant, evenZerofier, subgroup, field);
        // const result = evenInterpolant.fastMul(oddZerofier).add(oddInterpolant.fastMul(evenZerofier));
        if(times!=null) times[4] += Date.now()-startTime;

        return result;

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

    static zerofierPolynom(domain: bigint[], field: FiniteField): Polynom {

        const x = field.newVectorFrom([0n, 1n]);
        let acc = field.newVectorFrom([1n]);
        for(let d of domain) {
            acc = field.mulPolys(
                acc,
                field.subPolys(x, field.newVectorFrom([d]))
            );
        }

        return acc;
    }

    static zerofier(domain: bigint[], field: FiniteField): Polynomial {
        return new Polynomial(this.zerofierPolynom(domain, field), field);
    }

    static fastRecursiveZerofierPolynom(domain: bigint[], field: FiniteField, order?: number, cache?: ZerofierCache, threshold?: number): Polynom {

        if(domain.length<=threshold) return Polynomial.zerofierPolynom(domain, field);

        if(order==null) order = getNearestPowerOf2(domain.length);

        const evenPoints = domain.filter((_, index) => index%2===0);
        const oddPoints = domain.filter((_, index) => index%2===1);

        if(cache!=null) {
            cache.even = {children: {}};
            cache.odd = {children: {}};
        }
        const evenZerofier = Polynomial.fastRecursiveZerofierPolynom(evenPoints, field, order/2, cache.even.children, threshold);
        const oddZerofier = Polynomial.fastRecursiveZerofierPolynom(oddPoints, field, order/2, cache.odd.children, threshold);
        cache.even.poly = evenZerofier;
        cache.odd.poly = oddZerofier;

        return Polynomial.fastMulPolynom(evenZerofier, oddZerofier, field, order);

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

        const coefficients = lastLayer[0].toValues();

        let leadingIndex = 0;
        for(let i=coefficients.length-1;i>=0;i--) {
            if(coefficients[i]!==0n) {
                leadingIndex = i;
                break;
            }
        }

        return new Polynomial(field.newVectorFrom(coefficients.slice(0, leadingIndex+1)), field);

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

    splitAndFold(foldedSize: number, alpha: bigint) {

        const newCoefficients: bigint[] = Array<bigint>(foldedSize);

        for(let i=0;i<foldedSize;i++) {
            newCoefficients[i] = this.field.add(
                this.coefficients.getValue(2*i),
                this.field.mul(alpha, this.coefficients.getValue((2*i)+1))
            );
        }

        return new Polynomial(this.field.newVectorFrom(newCoefficients), this.field);

    }

}