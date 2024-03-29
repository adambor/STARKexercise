import {Field} from "./field/Field";
import * as galois from '@guildofweavers/galois';
import {Polynomial} from "./polynomial/Polynomial";
import {bigIntToBuffer, bufferToBigInt, MerkleTree} from "./merkle/MerkleTree";
import {Fri} from "./fri/Fri";
import {ProofStream} from "./fiatshamir/ProofStream";
import {PolynomialIOP} from "./polynomial/PolynomialIOP";
import exp from "constants";
import {Fibonacci} from "./programs/Fibonacci";
import {RescuePrime} from "./programs/RescuePrime";
import {MultiFri} from "./fri/MultiFri";
import {MultiMerkleTree} from "./merkle/MultiMerkleTree";
import {NumCompare} from "./programs/NumCompare";
import {generatorPoint, StarkSchnorr} from "./programs/StarkSchnorr";

// const fieldModulus = 407n * 2n ** 119n + 1n;
// const field = galois.createPrimeField(fieldModulus, false);
// const fieldGenerator = 85408008396924667383611388730472331217n;

const fieldModulus = 2n ** 251n + 17n * 2n ** 192n + 1n;
const field = galois.createPrimeField(fieldModulus, false);
const fieldGenerator = 3n;
const byteLength = 32;

function verifyPolyMul() {
    const poly = new Polynomial(field.newVectorFrom(Array.from({length: 10}, () => field.rand())), field);
    const poly2 = new Polynomial(field.newVectorFrom(Array.from({length: 10}, () => field.rand())), field);

    const start = Date.now();
    const result = poly.mul(poly2);
    console.log("Time: ", Date.now()-start);
}

function verifyPMTs() {

    const elements = Array.from({length: 10}, () => field.rand());
    const pmt = new MerkleTree(elements, 16);

    const index = 3;
    const root = pmt.commit();
    console.log("Root: ", root);
    const proof = pmt.open(index);
    console.log("Proof: ", proof);
    const verified = MerkleTree.verify(root, index, proof, elements[index], 16);
    console.log("Verified: ", verified);

}

function verifyFRI() {

    const polynomialDegree = 16*1024;
    const expansionFactor  = 4;
    const domainLength = polynomialDegree*expansionFactor;
    const omega = field.getRootOfUnity(domainLength);
    const fri = new MultiFri(fieldGenerator, omega, domainLength, field, expansionFactor, 64, 2);

    let startTime = Date.now();
    const poly3 = new Polynomial(field.newVectorFrom(Array.from({length: polynomialDegree}, (val, index) => {
        const buff = Buffer.alloc(4);
        buff.writeUintBE(index,0, 4);
        return field.prng(buff);
    })), field);

    // const codeword = poly3.evaluateAtRoots(field.getPowerSeries(omega, domainLength).toValues().map(val => field.mul(fieldGenerator, val)));
    // console.log("Computed polynomial at domain: ", Date.now()-startTime);
    //
    // const proofStream = new ProofStream([]);
    // fri.prove(codeword, proofStream, 16);
    // console.log("Compute FRI: ", Date.now()-startTime);

    const proofStream = new ProofStream([]);
    const initialIndices = fri.provePoly(poly3, proofStream, 16);
    console.log("Compute FRI: ", Date.now()-startTime);
    console.log("Initial FRI indices: ", initialIndices);

    const serialized = proofStream.serialize();
    console.log("Serialized proof length: ", serialized.length);

    startTime = Date.now();
    const topCodewordPoints = fri.verify(proofStream, 16);
    console.log("Verify FRI: ", Date.now()-startTime);

    // console.log(topCodewordPoints);

}

function verifyDegreeIOP() {

    let startTime = Date.now();

    const degreeBound = 1024;
    const polynomials: Polynomial[] = [];
    const degrees: number[] = [];
    for(let i=0;i<10;i++) {
        const polynomialDegree = Math.floor(Math.random()*degreeBound);
        degrees.push(polynomialDegree);
        const poly = new Polynomial(field.newVectorFrom(Array.from({length: polynomialDegree+1}, () => field.rand())), field);
        polynomials.push(poly);
    }

    console.log("Maximum polynomial degree: ", Math.max(...degrees));

    const proofStream = new ProofStream([]);

    const offset = fieldGenerator;
    const expansionFactor  = 4;
    const securityLevel = 128;
    const byteLength = 16;

    const polynomialCommitment = PolynomialIOP.proveDegrees(field, polynomials, offset, expansionFactor, securityLevel, byteLength, proofStream);

    console.log("Proof length: ", proofStream.serialize().length);

    PolynomialIOP.verifyDegrees(field, polynomialCommitment.map((val, index) => {
        return {
            commitment: val,
            degree: degrees[index]
        };
    }), offset, expansionFactor, securityLevel, byteLength, proofStream);

}

function verifyEvaluationIOP() {

    let startTime = Date.now();

    const offset = fieldGenerator;
    const expansionFactor = 4;
    const securityLevel = 128;
    const byteLength = 16;

    const polynomialDegree = 4*1024;
    const poly = new Polynomial(field.newVectorFrom(Array.from({length: polynomialDegree+1}, () => field.rand())), field);

    const x = 1n;
    const fX = poly.evaluate(x);

    console.log("Prove f("+x+")="+fX);

    const proofStream = new ProofStream([]);
    const polynomialCommitment = PolynomialIOP.proveEvaluation(poly, x, offset, expansionFactor, securityLevel, byteLength, proofStream);

    console.log("Proof length: ", proofStream.serialize().length);

    startTime = Date.now();
    PolynomialIOP.verifyEvaluation(field, polynomialCommitment, polynomialDegree, x, fX, offset, expansionFactor, securityLevel, byteLength, proofStream);
    console.log("Proof verify time: ", Date.now()-startTime);

}

function verifyRootsOfUnity() {

    const size = 8;

    const offset = fieldGenerator;
    const omega = field.getRootOfUnity(size);

    const points = field.getPowerSeries(omega, size).toValues();
    const pointsWithOffset = points.map(val => field.mul(val, offset));

    const randomVector = Array.from({length: size}, () => field.rand());
    console.log("Random vector: ", randomVector);
    const poly = new Polynomial(
        field.newVectorFrom(randomVector),
        field
    );

    const values1 = poly.evaluateDomain(pointsWithOffset);
    const values2 = poly.scale(offset).evaluateAtRoots(points);

    console.log(values1);
    console.log(values2);

}

function checkPolySpeed() {

    const degree = 16*1024;
    const evalDomain = 4*degree;
    const omega = field.getRootOfUnity(evalDomain);
    const powersOfOmega = field.getPowerSeries(omega, evalDomain).toValues();

    const poly1 = new Polynomial(
        field.newVectorFrom(Array.from({length: degree}, () => field.rand())),
        field
    );

    const poly2 = new Polynomial(
        field.newVectorFrom(Array.from({length: degree}, () => field.rand())),
        field
    );

    let startTime = Date.now();

    // const poly3 = poly1.mul(poly2);
    // poly3.evaluateAtRoots(powersOfOmega);
    //
    // console.log("Poly multiplication: ", Date.now()-startTime);

    startTime = Date.now();

    const codeword1 = poly1.evaluateAtRoots(powersOfOmega);
    const codeword2 = poly2.evaluateAtRoots(powersOfOmega);

    const resultCodeword = codeword1.map((val, index) => {
        return field.mul(val, codeword2[index]);
    });

    console.log("Codeword multiplication: ", Date.now()-startTime);

    const omicron = field.getRootOfUnity(2*degree);
    const omicronDomain = field.getPowerSeries(omicron, 2*degree).toValues();

    startTime = Date.now();

    const _codeword1 = poly1.evaluateAtRoots(omicronDomain);
    const _codeword2 = poly2.evaluateAtRoots(omicronDomain);

    const _resultCodeword = _codeword1.map((val, index) => {
        return field.mul(val, _codeword2[index]);
    });

    const _poly3 = Polynomial.interpolateAtRoots(omicronDomain, _resultCodeword, field);
    _poly3.evaluateAtRoots(powersOfOmega);

    console.log("Fast multiplication: ", Date.now()-startTime);

}

function checkStark() {


    const offset = fieldGenerator;
    const expansionFactor = 4;
    const securityLevel = 128;
    const byteLength = 16;

    const proveIndex = (4*1024)+1;

    let start = Date.now();
    const fibonacci = new Fibonacci(field, offset, byteLength, expansionFactor, securityLevel, 3);
    const fibResult = fibonacci.prove(proveIndex, true);
    console.log("Proving time: ", Date.now()-start);

    console.log("Fibonacci output: ", fibResult.output);

    const serializedProof = fibResult.proof.serialize();

    console.log("Serialized proof length: ", serializedProof.length);

    start = Date.now();
    console.log("Fibonacci verify...");
    fibonacci.verify(proveIndex, fibResult.output, fibResult.proof);
    console.log("Fibonacci verified in ", Date.now()-start);

}

function testZerofier() {

    const powersOfOmega = field.getPowerSeries(field.getRootOfUnity(8*1024), 8*1024);
    const zerofierDomainLength = 1875;
    const zerofierDomain = powersOfOmega.toValues().slice(845, 845+zerofierDomainLength);

    console.time("Zerofier");
    const originalZerofier = Polynomial.zerofier(zerofierDomain, field);
    console.timeEnd("Zerofier");

    console.time("Fast Zerofier");
    const fastZerofier = Polynomial.fastZerofier(zerofierDomain, field);
    console.timeEnd("Fast Zerofier");

    console.log(originalZerofier.degree());
    console.log(fastZerofier.degree());

    console.log(originalZerofier.evaluate(87213123n));
    console.log(fastZerofier.evaluate(87213123n));

}

function testPower() {

    const degree = 16;

    const poly1 = new Polynomial(
        field.newVectorFrom(Array.from({length: degree}, () => field.rand())),
        field
    );

    const result = poly1.power(2n);

    console.log("original: ", poly1.coefficients.toValues());
    console.log("original: ", result.coefficients.toValues());

}

function testFastEvaluate() {

    const degree = 8*845;
    const powersOfOmega = field.getPowerSeries(field.getRootOfUnity(8*1024), 8*1024);

    const values = Array.from({length: degree}, () => field.rand());

    // console.time("Normal interpolate");
    // const result1 = Polynomial.interpolateDomain(powersOfOmega.toValues().slice(0, degree), values, field);
    // console.timeEnd("Normal interpolate");

    console.time("FTT interpolate");
    const times = [0, 0, 0, 0, 0];
    const result2 = Polynomial.fastFFTInterpolate(powersOfOmega.toValues(), values, field, 1n, times);
    console.timeEnd("FTT interpolate");

    console.log("Times: ", times);

    // console.log(result1.coefficients.toValues());
    // console.log(result2.coefficients.toValues());

    // console.log(result1.evaluate(9812412412n));
    console.log(result2.evaluate(9812412412n));

    // const evalDomainLength = 1024;
    // const evalDomain = powersOfOmega.toValues().slice(0, evalDomainLength);
    //
    //
    // console.time("Normal eval");
    // const result1 = poly1.evaluateDomain(evalDomain);
    // console.timeEnd("Normal eval");
    //
    // console.time("Normal eval");
    // const result2 = poly1.evaluateDomainWithPoweringMap(evalDomain, powersOfOmega.toValues());
    // console.timeEnd("Normal eval");
    //
    // console.time("Normal eval");
    // const result3 = poly1.evaluateAtRoots(powersOfOmega.toValues()).slice(0, evalDomainLength);
    // console.timeEnd("Normal eval");
    //
    // const times = [0, 0, 0, 0, 0];
    // console.time("Fast eval");
    // const result4 = poly1.fastEvaluateDomain(evalDomain, fieldGenerator, times);
    // console.timeEnd("Fast eval");
    //
    // console.log("Times: ", times);

    // console.log(result1.coefficients.toValues().slice(550));
    // console.log(result2.coefficients.toValues().slice(1250));

    // const zeroDomain = [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n];
    // const zerofier = Polynomial.zerofier(zeroDomain, field);
    // console.log(zerofier.coefficients.toValues());
    // console.log(zerofier.evaluateDomain(zeroDomain));
    // console.log(result2);

}

function testAlternativeInterpolate() {

    const degree = 1024;
    const omega = field.getRootOfUnity(1024);
    const powersOfOmega = field.getPowerSeries(omega, 1024);
    const powersOfOmega2 = field.getPowerSeries(field.getRootOfUnity(512), 512);

    const values = Array.from({length: degree}, () => field.rand());

    const fastInterpolate = Polynomial.interpolateAtRoots(powersOfOmega2.toValues(), values.slice(0, 512), field);
    const fastInterpolateScaled = fastInterpolate.scale(omega);

    const normalInterpolate = Polynomial.interpolateDomain(powersOfOmega.toValues().slice(0, 512), values.slice(0, 512), field);

    console.log("Normal: ", normalInterpolate);
    console.log("Fast interpolate: ", fastInterpolateScaled);

}

function test() {

    const omega = field.getRootOfUnity(8);
    const powersOfOmega = field.getPowerSeries(omega, 8);

    const omega2 = field.getRootOfUnity(4);
    const powersOfOmega2 = field.getPowerSeries(omega2, 4);

    const values = Array.from({length: 4}, () => field.rand());

    const polynomial = new Polynomial(field.newVectorFrom(values), field);

    const allValues = polynomial.evaluateAtRoots(powersOfOmega.toValues());

    const evenTerms = polynomial.evaluateAtRoots(powersOfOmega2.toValues());
    const oddTerms = polynomial.scale(omega).evaluateAtRoots(powersOfOmega2.toValues());

    console.log(allValues);
    console.log(evenTerms);
    console.log(oddTerms);


}

function checkRescuePrime() {

    const offset = fieldGenerator;
    const expansionFactor = 4;
    const securityLevel = 128;
    const byteLength = 16;

    const m = 2;
    const alpha = 3n;
    const rounds = 27;

    let start = Date.now();
    const rescueHash = new RescuePrime(field, fieldModulus, offset, byteLength, expansionFactor, securityLevel, m, alpha, rounds);

    // console.log(rescueHash.getRoundConstants());
    console.log(rescueHash.prove(9274142n));
    console.log("Time: ", Date.now()-start);

}

function checkSubgroup() {

    const groupOrder = 16;
    const generator = field.getRootOfUnity(groupOrder);

    const element = field.exp(generator, 5n);

    console.log("Element raised to its order: ", field.exp(element, BigInt(groupOrder)));

}

function fastInterpolate0and1() {
    console.time("Fill array");
    const groupOrder = 128*1024;
    const values: bigint[] = [];
    for(let i=0;i<groupOrder;i++) {
        if(i<123*1024) {
            values[i] = 1n;
        } else {
            values[i] = 0n;
        }
    }
    const generator = field.getRootOfUnity(groupOrder);
    console.timeEnd("Fill array");

    console.time("Interpolate domain");
    const poly = Polynomial.interpolateAtRoots(field.getPowerSeries(generator, groupOrder).toValues(), values, field);
    console.log("Degree: ", poly.degree())
    console.timeEnd("Interpolate domain");

}

function sparseZerofier() {

    const groupOrder = 16;
    const generator = field.getRootOfUnity(groupOrder);

    const values: bigint[] = Array<bigint>(groupOrder);
    for(let i=0;i<groupOrder;i++) {
        values[i] = 0n;
    }
    values[groupOrder] = 1n;
    values[0] = field.neg(1n);
    const numerator = new Polynomial(field.newVectorFrom(values), field);
    const denominator = new Polynomial(field.newVectorFrom([
        field.neg(field.inv(generator)),
        1n
    ]), field);

    const zerofier = numerator.divide(denominator);

    const powersOfOmega = field.getPowerSeries(generator, groupOrder);

    console.log("Zerofier value: ", zerofier.evaluate(powersOfOmega.getValue(15)));

}

function verifyMultiPMTs() {

    const elements = Array.from({length: 16}, () => field.rand());
    const pmt = new MultiMerkleTree(elements.map(e => [e]), 16);

    const indices = [0, 8, 14];
    const root = pmt.commit();
    console.log("Root: ", root);
    console.log("Tree: ", pmt.layers);
    const proof = pmt.openMultiple(indices);
    console.log("Proof: ", proof);
    const verified = MultiMerkleTree.verifyMultiple(root, indices.map(index => {
        return {
            index: index,
            leaf: [elements[index]]
        }
    }), proof, 16);
    console.log("Verified: ", verified);
}

function checkNumCompare() {

    const comparator =  new NumCompare(field, fieldGenerator, byteLength, 4, 128, 1);

    const num1 = 8123122n;

    console.time("Stark prove");
    const proveData = comparator.prove(num1, 1n, 63, true);
    console.timeEnd("Stark prove");

    const proof = proveData.proof.serialize();

    console.log("Proof length: ", proof.length);

    console.time("Stark verify");
    comparator.verify(num1, 63, proveData.proof);
    console.timeEnd("Stark verify");

}

function schnorr() {

    const schnorr =  new StarkSchnorr(field, fieldGenerator, byteLength, 4, 128, 1);

    const privateKey = schnorr.randomKey();
    const publicKey = schnorr.toPublicKey(privateKey);

    const message = schnorr.randomKey();

    const signature = schnorr.sign(privateKey, message);
    const verification = schnorr.sigVerify(publicKey, message, signature);
    console.log("Signature verification: ", verification);

    const proof = schnorr.prove(signature.R, message, publicKey, true);
    schnorr.verify(signature.R, message, publicKey, proof.proof);

}

// verifyFRI();
//verifyRootsOfUnity();
// verifyDegreeIOP();
//verifyEvaluationIOP();
//checkPolySpeed();
// checkStark();
//testZerofier();
//testPower();
// testFastEvaluate();
// testAlternativeInterpolate();
// checkRescuePrime()
// checkSubgroup();
// fastInterpolate0and1();
// sparseZerofier();
// verifyMultiPMTs();
schnorr();

// test();

//console.log("Serialized proof: ", serialized.toString("hex"));
