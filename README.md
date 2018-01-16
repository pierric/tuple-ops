# tuple-ops
operations on n-ary tuples by manipulating via GHC.Generics. Current only uncons is implemented.

## uncons
```
> uncons (1::Int)
(1,())
```

```
> uncons (1::Int,'a')
(1,'a')
```

```
uncons (True,'a', "S")
(True,('a',"S"))
```

## design rational
uncons initially targets to work with C interfaces generated from C2HS. For example, the following definition  

```
{#fun MXSymbolInferShape as mxSymbolInferShapeImpl
    { id `SymbolHandle'
    , id `MXUInt'
    , withStringArray* `[String]'
    , withIntegralArray* `[Int]'
    , withIntegralArray* `[Int]'
    , alloca- `MXUInt' peek*
    , alloca- `Ptr MXUInt' peek*
    , alloca- `Ptr (Ptr MXUInt)' peek*
    , alloca- `MXUInt' peek*
    , alloca- `Ptr MXUInt' peek*
    , alloca- `Ptr (Ptr MXUInt)' peek*
    , alloca- `MXUInt' peek*
    , alloca- `Ptr MXUInt' peek*
    , alloca- `Ptr (Ptr MXUInt)' peek*
    , alloca- `Int' peekIntegral*
    } -> `Int' #}
```

generates a function that returns `(Int, MXUInt, Ptr MXUInt, Ptr (Ptr MXUInt), MXUInt, Ptr MXUInt, Ptr (Ptr MXUInt), 
MXUInt, Ptr MXUInt, Ptr (Ptr MXUInt), Int)`, in which the first element is return code. By `uncons` it, we can extract the
return code, throwing an exception when an error is indicated, and return the rest part as result.

`uncons` also fits  a function returning a return-code only. In this case, `()` is the result after extraction.

## limits
only tuple of size up to 16 is supported.

