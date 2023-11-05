import {Field} from "./field/Field";
import * as galois from '@guildofweavers/galois';
import {Polynomial} from "./polynomial/Polynomial";
import {bigIntToBuffer, bufferToBigInt, MerkleTree} from "./merkle/MerkleTree";
import {Fri} from "./fri/Fri";
import {ProofStream} from "./fiatshamir/ProofStream";
import {PolynomialIOP} from "./polynomial/PolynomialIOP";
import exp from "constants";

const field = galois.createPrimeField(407n * 2n ** 119n + 1n, false);
const fieldGenerator = 85408008396924667383611388730472331217n;

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
    const fri = new Fri(fieldGenerator, omega, domainLength, field, expansionFactor, 64);

    let startTime = Date.now();
    const poly3 = new Polynomial(field.newVectorFrom(Array.from({length: polynomialDegree}, () => field.rand())), field);

    const codeword = poly3.evaluateAtRoots(field.getPowerSeries(omega, domainLength).toValues().map(val => field.mul(fieldGenerator, val)));
    console.log("Computed polynomial at domain: ", Date.now()-startTime);

    const proofStream = new ProofStream([]);
    fri.prove(codeword, proofStream, 16);
    console.log("Compute FRI: ", Date.now()-startTime);

    const serialized = proofStream.serialize();
    console.log("Serialized proof length: ", serialized.length);

    startTime = Date.now();
    fri.verify(proofStream, 16);
    console.log("Verify FRI: ", Date.now()-startTime);

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

    PolynomialIOP.verifyEvaluation(field, polynomialCommitment, polynomialDegree, x, fX, offset, expansionFactor, securityLevel, byteLength, proofStream);

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

//verifyRootsOfUnity();
//verifyDegreeIOP();
verifyEvaluationIOP();

//console.log("Serialized proof: ", serialized.toString("hex"));
