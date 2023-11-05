
export class Field {

    readonly mod: bigint;

    constructor(mod: bigint) {
        this.mod = mod;
    }

    add(a: bigint, b: bigint): bigint {
        return (a+b)%this.mod;
    }

    sub(a: bigint, b: bigint): bigint {
        return (this.mod+a-b)%this.mod;
    }

    mul(a: bigint, b: bigint): bigint {
        return (a*b)%this.mod;
    }

    div(a: bigint, b: bigint): bigint {
        if(b===0n) throw new Error("Divide by zero");
        return (a*this.inverse(b))%this.mod;
    }

    pow(a: bigint, b: bigint): bigint {
        return (a**b)%this.mod;
    }

    negate(a: bigint): bigint {
        return (this.mod-(a%this.mod));
    }

    inverse(a: bigint): bigint {
        if(a==null) return null;
        let t = 0n;
        let r = this.mod;
        let newT = 1n;
        let newR = a;

        while(newR !== 0n) {
            const quotient = r/newR;
            const _newT = t - (quotient*newT);
            t = newT;
            newT = _newT;
            const _newR = r - (quotient*newR);
            r = newR;
            newR = _newR;
        }

        if(r>1n) {
            return null;
        }
        if(t<0n) {
            return t+this.mod;
        }
        return t;
    }

}