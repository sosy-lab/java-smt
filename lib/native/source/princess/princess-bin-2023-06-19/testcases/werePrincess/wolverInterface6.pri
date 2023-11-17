\problem {
\part[p0000] (((sym0=sym1) & (sym2=sym3) & (sym1=sym4) & (sym3=sym5) & (sym6=sym1) & (sym7=sym3))) &
\part[p0001] ((sym1>0)) &
\part[p0002] ((sym3>0)) &
\part[p0003] ((sym8=sym9)) &
\part[p0004] (!((sym8=0))) &
\part[p0005] (((sym10=addSigned(128, sym1, -1)) & (sym11=addSigned(128, sym3, 1)))) &
\part[p0006] (true) &
\part[p0007] (((sym12=sym10) & (sym13=sym11) & (!((addSigned(8192, addSigned(2048, mulSigned(512, sym10, -1), sym11), -1)>=addSigned(8192, addSigned(2048, mulSigned(512, sym6, -1), sym7), -1))) | !((addSigned(8192, sym10, -1)>=addSigned(8192, sym6, -1)))))) &

\part[p0008] ((sym10>0)) &
\part[p0009] ((sym11>0)) &
\part[p0010] ((sym14=sym15)) &
\part[p0011] (!((sym14=0))) &
\part[p0012] (((sym16=addSigned(128, sym10, -1)) & (sym17=addSigned(128, sym11, 1)))) &
\part[p0013] (true) &
\part[p0014] ((!((addSigned(8192, addSigned(2048, mulSigned(512, sym16, -1), sym17), -1)>=addSigned(8192, addSigned(2048, mulSigned(512, sym12, -1), sym13), -1))) | !((addSigned(8192, sym16, -1)>=addSigned(8192, sym12, -1))))) &
\part[p0015] (((addSigned(8192, addSigned(2048, mulSigned(512, sym16, -1), sym17), -1)>=addSigned(8192, addSigned(2048, mulSigned(512, sym0, -1), sym2), -1)) & 
(addSigned(8192, sym16, -1)>=addSigned(8192, sym0, -1)))) &


inSigned(128, sym0) & 
inSigned(128, sym1) & 
inSigned(128, sym10) & 
inSigned(128, sym11) & 
inSigned(128, sym12) & 
inSigned(128, sym13) & 
inSigned(2*1024*1024*1024, sym14) & 
inSigned(2*1024*1024*1024, sym15) & 
inSigned(128, sym16) & 
inSigned(128, sym17) & 
inSigned(128, sym2) & 
inSigned(128, sym3) & 
inSigned(128, sym4) & 
inSigned(128, sym5) & 
inSigned(128, sym6) & 
inSigned(128, sym7) & 
inSigned(2*1024*1024*1024, sym8) & 
inSigned(2*1024*1024*1024, sym9)
-> false
}
\functions {
int sym0, sym1, sym10, sym11, sym12, sym13, sym14, sym15, sym16, sym17, sym2, sym3, sym4, sym5, sym6, sym7, sym8, sym9;
}
