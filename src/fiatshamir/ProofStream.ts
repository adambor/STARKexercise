import * as crypto from "crypto";
import {bigIntToBuffer, bufferToBigInt} from "../merkle/MerkleTree";


export class ProofStream {

    objects: Buffer[] = [];
    readIndex: number = 0;
    hashCache: Buffer[] = [];

    proverRandomnessQueryCounts: number = 0;
    verifierRandomnessQueryCounts: number = 0;

    constructor(objects: Buffer[]) {
        this.objects = objects;
    }

    push(data: Buffer) {
        this.objects.push(data);
    }

    pushBigInt(value: bigint, byteLength: number) {
        this.push(bigIntToBuffer(value, byteLength));
    }

    pushBigInts(values: bigint[], byteLength: number) {
        this.push(Buffer.concat(values.map(val => bigIntToBuffer(val, byteLength))))
    }

    pull(): Buffer {
        const val = this.objects[this.readIndex];
        if(val==null) return null;
        this.readIndex++;
        return val;
    }

    pullBigInt(): bigint {
        return bufferToBigInt(this.pull());
    }

    pullBigInts(byteLength: number): bigint[] {
        const buff = this.pull();
        const arr = Array<bigint>(buff.length/byteLength);
        for(let i=0;i<arr.length;i++) {
            const startPosition = i*byteLength;
            arr[i] = bufferToBigInt(buff.subarray(startPosition, startPosition+byteLength));
        }
        return arr;
    }

    serialize(endIndex?: number): Buffer {
        const buffArr = [];
        this.objects.forEach((obj, index) => {
            if(endIndex!=null && index>=endIndex) return;
            const prefix = Buffer.alloc(4);
            prefix.writeUintLE(obj.length, 0, 4);
            buffArr.push(prefix, obj);
        });
        return Buffer.concat(buffArr);
    }

    hash(endIndex?: number): Buffer {
        const buffArr = [];
        this.objects.forEach((obj, index) => {
            if(endIndex!=null && index>=endIndex) return;
            const prefix = Buffer.alloc(4);
            prefix.writeUintLE(obj.length, 0, 4);
            buffArr.push(prefix, obj);
        });
        if(this.hashCache[endIndex || this.objects.length]==null) {
            this.hashCache[endIndex || this.objects.length] = crypto.createHash("sha256").update(Buffer.concat(buffArr)).digest();
        }
        return this.hashCache[endIndex || this.objects.length];
    }

    proverFiatShamir(): Buffer {
        this.proverRandomnessQueryCounts++;
        const buff = Buffer.alloc(6);
        buff.writeUIntBE(this.proverRandomnessQueryCounts, 0, 6);
        return crypto.createHash("sha256").update(Buffer.concat([
            this.hash(),
            buff
        ])).digest();
    }

    verifierFiatShamir(): Buffer {
        this.verifierRandomnessQueryCounts++;
        const buff = Buffer.alloc(6);
        buff.writeUIntBE(this.verifierRandomnessQueryCounts, 0, 6);
        return crypto.createHash("sha256").update(Buffer.concat([
            this.hash(this.readIndex),
            buff
        ])).digest();
    }

    static deserialize(buff: Buffer): ProofStream {
        let pointer = 0;
        const objects: Buffer[] = [];
        while(pointer<buff.length) {
            const objectLength = buff.readUintLE(pointer, 4);
            objects.push(buff.subarray(pointer+4, pointer+objectLength+4));
            pointer += 4+objectLength;
        }
        return new ProofStream(objects);
    }

}