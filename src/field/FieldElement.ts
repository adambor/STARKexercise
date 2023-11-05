import {Field} from "./Field";

export class FieldElement {

    readonly field: Field;
    readonly value: bigint;

    constructor(val: bigint, field: Field) {
        this.value = val;
        this.field = field;
    }

    add(b: FieldElement): FieldElement {
        return new FieldElement(this.field.add(this.value, b.value), this.field);
    }

}