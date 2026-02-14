enum Operations {
    OPBR = 0, /* branch */
    OPADD,    /* add  */
    OPLD,     /* load */
    OPST,     /* store */
    OPJSR,    /* jump register */
    OPAND,    /* bitwise and */
    OPLDR,    /* load register */
    OPSTR,    /* store register */
    OPRTI,    /* unused */
    OPNOT,    /* bitwise not */
    OPLDI,    /* load indirect */
    OPSTI,    /* store indirect */
    OPJMP,    /* jump */
    OPRES,    /* reserved (unused) */
    OPLEA,    /* load effective address */
    OPTRAP,   /* execute trap */
}
