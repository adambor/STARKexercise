import * as crypto from "crypto";
import {bigIntToBuffer} from "./MerkleTree";

const algorithm = "sha256";

export class MultiMerkleTree {

    layers: Buffer[][] = [];
    leafs: bigint[][];

    constructor(leafs: bigint[][], byteLength: number) {
        this.leafs = leafs;
        this.layers.push(leafs.map(leaf => crypto.createHash(algorithm).update(
            Buffer.concat(leaf.map(element => bigIntToBuffer(element, byteLength)))
        ).digest()));
        while(this.layers[this.layers.length-1].length>1) {
            const lastLayer = this.layers[this.layers.length-1];
            const len = lastLayer.length;
            const nextLen = Math.ceil(len/2);
            const nextLayer = Array<Buffer>(nextLen);
            for(let i=0;i<nextLen;i++) {
                const left = 2*i;
                const right = left + 1 < len ? left + 1 : left;
                nextLayer[i] = crypto.createHash(algorithm).update(Buffer.concat([lastLayer[left], lastLayer[right]])).digest();
            }
            this.layers.push(nextLayer);
        }
    }

    commit(): Buffer {
        return this.layers[this.layers.length-1][0];
    }

    open(index: number): Buffer[] {
        const path: Buffer[] = [];

        while(path.length<this.layers.length-1) {
            const position = index & 0b1; //0 - left, 1 - right
            const layer = this.layers[path.length];
            if(position===0) {
                path.push(index+1 < layer.length ? layer[index+1] : layer[index]);
            } else {
                path.push(layer[index-1]);
            }
            index = index >> 1;
        }

        return path;
    }

    openBuffer(index: number): Buffer {
        return Buffer.concat(this.open(index));
    }

    static verify(root: Buffer, index: number, _path: Buffer[] | Buffer, leaf: bigint[], byteLength: number) {

        let path: Buffer[];
        if(!Array.isArray(_path)) {
            const size = _path.length/32;
            path = Array<Buffer>(size);
            for(let i=0;i<size;i++) {
                path[i] = _path.subarray(i*32, (i+1)*32);
            }
        } else {
            path = _path;
        }

        let hash: Buffer = crypto.createHash(algorithm).update(
            Buffer.concat(leaf.map(element => bigIntToBuffer(element, byteLength)))
        ).digest();
        for(let pathFragment of path) {
            const position = index & 0b1; //0 - left, 1 - right
            let arr: Buffer[];
            if(position===0) {
                arr = [hash, pathFragment];
            } else {
                arr = [pathFragment, hash];
            }
            hash = crypto.createHash(algorithm).update(Buffer.concat(arr)).digest();
            index = index >> 1;
        }

        return hash.equals(root);

    }

}
