import * as crypto from "crypto";
import {bigIntToBuffer} from "./MerkleTree";
import has = Reflect.has;

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

    openMultiple(_indices: number[]): Buffer[] {
        const indices = [..._indices];

        const path: Buffer[] = [];

        let knownLastLayerIndices: Set<number> = new Set<number>(indices);

        for(let i=1;i<this.layers.length;i++) {
            indices.forEach((val, index) => indices[index] = val >> 1);

            for(let index of indices) {
                const left = index*2;
                const right = (index*2) + 1;

                if(!knownLastLayerIndices.has(left)) {
                    path.push(this.layers[i-1][left]);
                    knownLastLayerIndices.add(left);
                }
                if(!knownLastLayerIndices.has(right)) {
                    path.push(this.layers[i-1][right]);
                    knownLastLayerIndices.add(right);
                }
            }

            knownLastLayerIndices = new Set<number>(indices);
        }

        return path;
    }

    openBuffer(index: number): Buffer {
        return Buffer.concat(this.open(index));
    }

    openMultipleBuffer(indices: number[]): Buffer {
        return Buffer.concat(this.openMultiple(indices));
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

    static verifyMultiple(
        root: Buffer,
        elements: {
            index: number,
            leaf: bigint[]
        }[],
        _path: Buffer[] | Buffer,
        byteLength: number
    ) {

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

        let lastLayerBuffers: Buffer[] = [];
        let indices: number[] = Array<number>(elements.length);

        elements.forEach((element, index) => {
            lastLayerBuffers[element.index] = crypto.createHash(algorithm).update(
                Buffer.concat(element.leaf.map(e => bigIntToBuffer(e, byteLength)))
            ).digest();
            indices[index] = element.index;
        });

        let counter = 0;

        while(true) {
            indices.forEach((val, index) => indices[index] = val >> 1);

            let currentLayerBuffers: Buffer[] = [];
            for(let index of indices) {
                if(currentLayerBuffers[index]!=null) continue;

                const left = index*2;
                const right = left + 1;

                let leftBuffer = lastLayerBuffers[left];
                let rightBuffer = lastLayerBuffers[right];
                if(leftBuffer==null) {
                    if(counter>=path.length) {
                        currentLayerBuffers = null;
                        break;
                    }
                    leftBuffer = path[counter];
                    counter++;
                    lastLayerBuffers[left] = leftBuffer;
                }
                if(rightBuffer==null) {
                    if(counter>=path.length) {
                        currentLayerBuffers = null;
                        break;
                    }
                    rightBuffer = path[counter];
                    counter++;
                    lastLayerBuffers[right] = rightBuffer;
                }

                const hash = crypto.createHash(algorithm).update(Buffer.concat([leftBuffer, rightBuffer])).digest();

                currentLayerBuffers[index] = hash;
            }

            if(currentLayerBuffers==null) break;

            lastLayerBuffers = currentLayerBuffers;
        }

        if(lastLayerBuffers[0]==null) return false;

        return lastLayerBuffers[0].equals(root);

    }

}
