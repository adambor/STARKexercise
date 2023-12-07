import {FiniteField} from "@guildofweavers/galois";


export function fastExp(bases: bigint[], exponents: number[], field: FiniteField, cache?: bigint[]) {

    if(cache==null) cache = [];

    let highestExp = Math.max(...exponents);
    let val = 1;
    let count = -1;
    while(highestExp>=val) {
        val = val << 1;
        count++;
    }

    let result = 1n;
    for(let i=count;i>=0;i--) {
        result = field.mul(result, result);

        let cacheIndex: number = 0;
        exponents.forEach((exponent, index) => {
            cacheIndex |= (exponent>>i & 0b1) << index;
        });

        let val = cache[cacheIndex];

        if(val==null) {
            val = 1n;
            bases.forEach((base, index) => {
                if((cacheIndex>>index & 0b1)===1) {
                    val = field.mul(val, base);
                }
            });
            cache[cacheIndex] = val;
        }

        result = field.mul(result, val);
    }

    return result;

}