You said:
set options:
set_option diagnostics.threshold 100
set_option diagnostics true
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.isDefEq true
set_option trace.linarith true
set_option trace.compiler.ir.result true
set_option autoImplicit false
set_option maxRecDepth 1000

Lots of errors and diagnostics:
Termination.lean:567:33
Messages (3)
All Messages (326)
Termination.lean:117:17
[Meta.isDefEq] ✅️ Sort ?u.16010 =?= Type
Termination.lean:117:17
[Meta.isDefEq] ✅️ Sort ?u.16178 =?= Type
Termination.lean:117:17
[Meta.isDefEq] ✅️ Sort ?u.16418 =?= Type
Termination.lean:117:17
[Meta.isDefEq] ✅️ Sort ?u.17041 =?= Type
Termination.lean:117:17
[Meta.isDefEq] ✅️ Sort ?u.17666 =?= Type
Termination.lean:117:25
[Meta.isDefEq] ✅️ Sort ?u.16012 =?= Type
Termination.lean:117:25
[Meta.isDefEq] ✅️ Sort ?u.16180 =?= Type
Termination.lean:117:25
[Meta.isDefEq] ✅️ Sort ?u.16420 =?= Type
Termination.lean:117:25
[Meta.isDefEq] ✅️ Sort ?u.17043 =?= Type
Termination.lean:117:25
[Meta.isDefEq] ✅️ Sort ?u.17668 =?= Type
Termination.lean:567:4
failed to compile definition, compiler IR check failed at 'MetaSN.bigA'. Error: depends on declaration 'Ordinal.instPow', which has no executable code; consider marking definition as 'noncomputable'
Termination.lean:567:14
[Meta.isDefEq] ✅️ Sort ?u.16015 =?= Type
Termination.lean:567:23
[Meta.isDefEq] ✅️ Sort ?u.16017 =?= Type (?u.16018 + 1)
Termination.lean:568:16
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:568:22
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:568:15
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:568:12
[Meta.isDefEq] ✅️ Type ?u.16052 =?= Type (?u.16029 + 1)
[Meta.isDefEq] ✅️ Type ?u.16053 =?= Type (?u.16029 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.16054) =?= Type (?u.16029 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16029} Ordinal.{?u.16029} ?m.16055 =?= HAdd ?m.16058 ?m.16058 ?m.16058 ▶
[Meta.isDefEq] ✅️ ?m.16056 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16029} =?= Add Ordinal.{?u.16072} ▶
[Meta.isDefEq] ✅️ ?m.16059 =?= add ▶
[Meta.isDefEq] ✅️ ?m.16059 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16029} Ordinal.{?u.16029}
Ordinal.{?u.16029} =?= HAdd Ordinal.{?u.16029} Ordinal.{?u.16029} Ordinal.{?u.16029}
[Meta.isDefEq] ✅️ Type (?u.16029 + 1) =?= Type (?u.16029 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16029} =?= Add Ordinal.{?u.16029}
[Meta.isDefEq] ✅️ Ordinal.{?u.16029} =?= Ordinal.{?u.16029}
[Meta.isDefEq] ✅️ Ordinal.{?u.16029} =?= ?m.16031 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16029} =?= ?m.16075 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16029} =?= ?m.16076 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16029} Ordinal.{?u.16029} ?m.16079 =?= HAdd ?m.16082 ?m.16082 ?m.16082 ▶
[Meta.isDefEq] ✅️ ?m.16080 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16029} =?= Add Ordinal.{?u.16093} ▶
[Meta.isDefEq] ✅️ ?m.16083 =?= add ▶
[Meta.isDefEq] ✅️ ?m.16083 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16029} Ordinal.{?u.16029} ?m.16077 =?= HAdd Ordinal.{?u.16029} Ordinal.{?u.16029} Ordinal.{?u.16029} ▶
[Meta.isDefEq] ✅️ Type (?u.16029 + 1) =?= Type (?u.16029 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16029} =?= Add Ordinal.{?u.16029}
[Meta.isDefEq] ✅️ ?m.16078 =?= instHAdd ▶
Termination.lean:568:27
[Meta.isDefEq] 💥️ OfNat ?m.16031 6 =?= OfNat ℕ+ ?m.16040 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16031 6 =?= OfNat ℕ+ ?m.16050 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16029} 6 =?= OfNat ?m.16103 ?m.16104 ▶
[Meta.isDefEq] ✅️ ?m.16100 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16029} =?= NatCast ?m.16110 ▶
[Meta.isDefEq] ✅️ ?m.16105 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16029} =?= AddMonoidWithOne Ordinal.{?u.16116} ▶
[Meta.isDefEq] ✅️ ?m.16111 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16111 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16105 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (?m.16119 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16106 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16106 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16029} 6 =?= OfNat Ordinal.{?u.16029} 6
[Meta.isDefEq] ✅️ Type (?u.16029 + 1) =?= Type (?u.16029 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.16029 + 1) =?= Type (?u.16029 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16029} =?= AddMonoidWithOne Ordinal.{?u.16029}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16029} =?= NatCast Ordinal.{?u.16029}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 4 =?= OfNat ℕ 4
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (4 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16033 =?= instOfNatAtLeastTwo ▶
Termination.lean:568:2
[Meta.isDefEq] 💥️ Ordinal.{?u.16018} =?= Ordinal.{?u.16025}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16025} x Ordinal.{?u.16018} =?= CoeT ?m.16132 ?m.16133 ?m.16132 ▶
[Meta.isDefEq] ✅️ ?m.16126 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16025} x Ordinal.{?u.16018} =?= CoeT Ordinal.{?u.16025} x Ordinal.{?u.16025} ▶
[Meta.isDefEq] ✅️ Type (?u.16025 + 1) =?= Type (?u.16025 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.16025} =?= Ordinal.{?u.16025}
[Meta.isDefEq] ✅️ Ordinal.{?u.16025} =?= Ordinal.{?u.16025}
[Meta.isDefEq] ✅️ Ordinal.{?u.16025} =?= Ordinal.{?u.16025}
[Meta.isDefEq] ✅️ Ordinal.{?u.16025} =?= ?m.16143 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16029} =?= ?m.16144 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16025} Ordinal.{?u.16029} ?m.16147 =?= HPow ?m.16151 ?m.16152 ?m.16151 ▶
[Meta.isDefEq] ✅️ ?m.16148 =?= instHPow ▶
[Meta.isDefEq] ✅️ Pow Ordinal.{?u.16025} Ordinal.{?u.16029} =?= Pow Ordinal.{?u.16161} Ordinal.{?u.16161} ▶
[Meta.isDefEq] ✅️ ?m.16153 =?= instPow ▶
[Meta.isDefEq] ✅️ ?m.16153 =?= instPow ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16025} Ordinal.{?u.16029} ?m.16145 =?= HPow Ordinal.{?u.16025} Ordinal.{?u.16025} Ordinal.{?u.16025} ▶
[Meta.isDefEq] ✅️ Type (?u.16025 + 1) =?= Type (?u.16025 + 1)
[Meta.isDefEq] ✅️ Type (?u.16025 + 1) =?= Type (?u.16025 + 1)
[Meta.isDefEq] ✅️ Pow Ordinal.{?u.16025} Ordinal.{?u.16025} =?= Pow Ordinal.{?u.16025} Ordinal.{?u.16025}
[Meta.isDefEq] ✅️ ?m.16146 =?= instHPow ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16025} =?= Ordinal.{?u.16025} ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16025} =?= Ordinal.{?u.16025} ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16025} =?= Ordinal.{?u.16025} ▶
Termination.lean:570:19
[Meta.isDefEq] ✅️ Sort ?u.16183 =?= Type
Termination.lean:570:28
[Meta.isDefEq] ✅️ Ordinal.{?u.16213} =?= Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ Ordinal.{?u.16213} =?= ?m.16240 ▶
[Meta.isDefEq] ✅️ ?m.16192 =?= ?m.16241 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16213} ?m.16241 ?m.16244 =?= HPow ?m.16249 ?m.16250 ?m.16249 ▶
[Meta.isDefEq] ✅️ ?m.16245 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16213} ?m.16241 =?= Pow Ordinal.{?u.16266} Ordinal.{?u.16266} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16213} ?m.16241 ?m.16304 =?= HPow ?m.16309 ?m.16310 ?m.16309 ▶
[Meta.isDefEq] ✅️ ?m.16305 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16213} ?m.16241 =?= Pow Ordinal.{?u.16323} Ordinal.{?u.16323} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16213} ?m.16241 ?m.16332 =?= HPow ?m.16337 ?m.16338 ?m.16337 ▶
[Meta.isDefEq] ✅️ ?m.16333 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16213} ?m.16241 =?= Pow Ordinal.{?u.16348} Ordinal.{?u.16348} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16213} ?m.16241 ?m.16357 =?= HPow ?m.16362 ?m.16363 ?m.16362 ▶
[Meta.isDefEq] ✅️ ?m.16358 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16213} ?m.16241 =?= Pow Ordinal.{?u.16373} Ordinal.{?u.16373} ▶
[Meta.isDefEq] ✅️ ?m.16243 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16213} ?β =?= Pow Ordinal.{?u.16391} Ordinal.{?u.16391} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.16213} =?= Monoid Ordinal.{?u.16405} ▶
[Meta.isDefEq] ✅️ ?m.16399 =?= monoid ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.16213} =?= Monoid Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:570:37
[Meta.isDefEq] 💥️ OfNat ?m.16192 3 =?= OfNat ℕ+ ?m.16201 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16192 3 =?= OfNat ℕ+ ?m.16211 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16192 3 =?= OfNat ℕ+ ?m.16220 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16241 3 =?= OfNat ℕ+ ?m.16300 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16241 3 =?= OfNat ℕ+ ?m.16330 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16241 3 =?= OfNat ℕ+ ?m.16355 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ ?m.16411 ▶
[Meta.isDefEq] ✅️ ?m.16408 =?= instOfNatNat 3 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ 3
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ?m.16194 =?= instOfNatNat 3 ▶
Termination.lean:570:28
[Meta.isDefEq] 💥️ Ordinal.{?u.16190} =?= Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16213} x Ordinal.{?u.16190} =?= CoeT ?m.16229 ?m.16230 ?m.16229 ▶
[Meta.isDefEq] ✅️ ?m.16223 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16213} x Ordinal.{?u.16190} =?= CoeT Ordinal.{?u.16213} x Ordinal.{?u.16213} ▶
[Meta.isDefEq] ✅️ Type (?u.16213 + 1) =?= Type (?u.16213 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.16213} =?= Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ Ordinal.{?u.16213} =?= Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ Ordinal.{?u.16213} =?= Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ ?m.16242 =?= ?m.16269 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16213} =?= ?m.16269 ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.16213} =?= LT ?m.16274 ▶
[Meta.isDefEq] ✅️ ?m.16271 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16213} =?= Preorder ?m.16278 ▶
[Meta.isDefEq] ✅️ ?m.16275 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16213} =?= PartialOrder Ordinal.{?u.16290} ▶
[Meta.isDefEq] ✅️ ?m.16279 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16279 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16275 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.16213} =?= LT Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ Type (?u.16213 + 1) =?= Type (?u.16213 + 1)
[Meta.isDefEq] ✅️ Type (?u.16213 + 1) =?= Type (?u.16213 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16213} =?= PartialOrder Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16213} =?= Preorder Ordinal.{?u.16213}
[Meta.isDefEq] ✅️ ?m.16270 =?= partialOrder.toLT ▶
Termination.lean:570:46
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:572:2
[Meta.isDefEq] ✅️ 3 < mu n.delta + 6 =?= 3 < mu n.delta + 6
[Meta.isDefEq] ✅️ ω ^ 3 < bigA n =?= ω ^ 3 < bigA n
[Meta.isDefEq] ✅️ ω ^ 3 < bigA n =?= ω ^ 3 < bigA n ▶
Termination.lean:572:23
[Meta.isDefEq] ✅️ Ordinal.{?u.16424} =?= ?m.16426 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16424} 3 =?= OfNat ?m.16431 ?m.16432 ▶
[Meta.isDefEq] ✅️ ?m.16428 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16424} =?= NatCast ?m.16438 ▶
[Meta.isDefEq] ✅️ ?m.16433 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16424} =?= AddMonoidWithOne Ordinal.{?u.16444} ▶
[Meta.isDefEq] ✅️ ?m.16439 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16439 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16433 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 3 =?= (?m.16447 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16434 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16434 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16424} 3 =?= OfNat Ordinal.{?u.16424} 3
[Meta.isDefEq] ✅️ Type (?u.16424 + 1) =?= Type (?u.16424 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.16424 + 1) =?= Type (?u.16424 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16424} =?= AddMonoidWithOne Ordinal.{?u.16424}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16424} =?= NatCast Ordinal.{?u.16424}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 1 =?= OfNat ℕ 1
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 3 =?= (1 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16427 =?= instOfNatAtLeastTwo ▶
Termination.lean:572:27
[Meta.isDefEq] ✅️ Sort ?u.16423 =?= Type (?u.16424 + 1)
Termination.lean:572:22
[Meta.isDefEq] ✅️ Ordinal.{?u.16424} =?= Ordinal.{?u.16424}
Termination.lean:572:42
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:572:48
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:572:41
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:572:22
[Meta.isDefEq] 💥️ Ordinal.{?u.16424} =?= Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16456} x Ordinal.{?u.16424} =?= CoeT ?m.16486 ?m.16487 ?m.16486 ▶
[Meta.isDefEq] ✅️ ?m.16480 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16456} x Ordinal.{?u.16424} =?= CoeT Ordinal.{?u.16456} x Ordinal.{?u.16456} ▶
[Meta.isDefEq] ✅️ Type (?u.16456 + 1) =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= ?m.16545 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ LT Ordinal.{?u.16456} =?= LT ?m.16550 ▶
[Meta.isDefEq] ✅️ ?m.16547 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16456} =?= Preorder ?m.16554 ▶
[Meta.isDefEq] ✅️ ?m.16551 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16456} =?= PartialOrder Ordinal.{?u.16566} ▶
[Meta.isDefEq] ✅️ ?m.16555 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16555 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16551 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.16456} =?= LT Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Type (?u.16456 + 1) =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ Type (?u.16456 + 1) =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16456} =?= PartialOrder Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16456} =?= Preorder Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ ?m.16546 =?= partialOrder.toLT ▶
Termination.lean:572:38
[Meta.isDefEq] ✅️ Type ?u.16497 =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ Type ?u.16498 =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.16499) =?= Type (?u.16456 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16456} Ordinal.{?u.16456} ?m.16500 =?= HAdd ?m.16503 ?m.16503 ?m.16503 ▶
[Meta.isDefEq] ✅️ ?m.16501 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16456} =?= Add Ordinal.{?u.16517} ▶
[Meta.isDefEq] ✅️ ?m.16504 =?= add ▶
[Meta.isDefEq] ✅️ ?m.16504 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16456} Ordinal.{?u.16456}
Ordinal.{?u.16456} =?= HAdd Ordinal.{?u.16456} Ordinal.{?u.16456} Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Type (?u.16456 + 1) =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16456} =?= Add Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= ?m.16458 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= ?m.16520 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16456} =?= ?m.16521 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16456} Ordinal.{?u.16456} ?m.16524 =?= HAdd ?m.16527 ?m.16527 ?m.16527 ▶
[Meta.isDefEq] ✅️ ?m.16525 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16456} =?= Add Ordinal.{?u.16538} ▶
[Meta.isDefEq] ✅️ ?m.16528 =?= add ▶
[Meta.isDefEq] ✅️ ?m.16528 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16456} Ordinal.{?u.16456} ?m.16522 =?= HAdd Ordinal.{?u.16456} Ordinal.{?u.16456} Ordinal.{?u.16456} ▶
[Meta.isDefEq] ✅️ Type (?u.16456 + 1) =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16456} =?= Add Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ ?m.16523 =?= instHAdd ▶
Termination.lean:572:53
[Meta.isDefEq] 💥️ OfNat ?m.16458 6 =?= OfNat ℕ+ ?m.16467 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16458 6 =?= OfNat ℕ+ ?m.16477 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16456} 6 =?= OfNat ?m.16573 ?m.16574 ▶
[Meta.isDefEq] ✅️ ?m.16570 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16456} =?= NatCast ?m.16580 ▶
[Meta.isDefEq] ✅️ ?m.16575 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16456} =?= AddMonoidWithOne Ordinal.{?u.16586} ▶
[Meta.isDefEq] ✅️ ?m.16581 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16581 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16575 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (?m.16589 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16576 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16576 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16456} 6 =?= OfNat Ordinal.{?u.16456} 6
[Meta.isDefEq] ✅️ Type (?u.16456 + 1) =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.16456 + 1) =?= Type (?u.16456 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16456} =?= AddMonoidWithOne Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16456} =?= NatCast Ordinal.{?u.16456}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 4 =?= OfNat ℕ 4
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (4 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16460 =?= instOfNatAtLeastTwo ▶
Termination.lean:573:4
[Meta.isDefEq] ✅️ 3 < 6 =?= 3 < 6
[Meta.isDefEq] ✅️ 3 < mu n.delta + 6 =?= 3 < mu n.delta + 6
[Meta.isDefEq] ✅️ 3 < mu n.delta + 6 =?= 3 < mu n.delta + 6 ▶
Termination.lean:573:12
[Meta.isDefEq] ✅️ Ordinal.{?u.16600} =?= ?m.16602 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16600} 3 =?= OfNat ?m.16607 ?m.16608 ▶
[Meta.isDefEq] ✅️ ?m.16604 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16600} =?= NatCast ?m.16614 ▶
[Meta.isDefEq] ✅️ ?m.16609 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16600} =?= AddMonoidWithOne Ordinal.{?u.16620} ▶
[Meta.isDefEq] ✅️ ?m.16615 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16615 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16609 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 3 =?= (?m.16623 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16610 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16610 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16600} 3 =?= OfNat Ordinal.{?u.16600} 3
[Meta.isDefEq] ✅️ Type (?u.16600 + 1) =?= Type (?u.16600 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.16600 + 1) =?= Type (?u.16600 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16600} =?= AddMonoidWithOne Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16600} =?= NatCast Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 1 =?= OfNat ℕ 1
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 3 =?= (1 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16603 =?= instOfNatAtLeastTwo ▶
Termination.lean:573:16
[Meta.isDefEq] ✅️ Sort ?u.16599 =?= Type (?u.16600 + 1)
Termination.lean:573:11
[Meta.isDefEq] ✅️ Ordinal.{?u.16600} =?= Ordinal.{?u.16600}
Termination.lean:573:11
[Meta.isDefEq] ✅️ Ordinal.{?u.16600} =?= Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ Ordinal.{?u.16600} =?= ?m.16627 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16600} =?= ?m.16648 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16600} =?= Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ LT Ordinal.{?u.16600} =?= LT ?m.16653 ▶
[Meta.isDefEq] ✅️ ?m.16650 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16600} =?= Preorder ?m.16657 ▶
[Meta.isDefEq] ✅️ ?m.16654 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16600} =?= PartialOrder Ordinal.{?u.16669} ▶
[Meta.isDefEq] ✅️ ?m.16658 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16658 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16654 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.16600} =?= LT Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ Type (?u.16600 + 1) =?= Type (?u.16600 + 1)
[Meta.isDefEq] ✅️ Type (?u.16600 + 1) =?= Type (?u.16600 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16600} =?= PartialOrder Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16600} =?= Preorder Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ ?m.16649 =?= partialOrder.toLT ▶
Termination.lean:573:27
[Meta.isDefEq] 💥️ OfNat ?m.16627 6 =?= OfNat ℕ+ ?m.16636 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16627 6 =?= OfNat ℕ+ ?m.16646 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16600} 6 =?= OfNat ?m.16676 ?m.16677 ▶
[Meta.isDefEq] ✅️ ?m.16673 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16600} =?= NatCast ?m.16681 ▶
[Meta.isDefEq] ✅️ ?m.16678 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16600} =?= AddMonoidWithOne Ordinal.{?u.16685} ▶
[Meta.isDefEq] ✅️ ?m.16682 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16682 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16678 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (?m.16686 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16679 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16679 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16600} 6 =?= OfNat Ordinal.{?u.16600} 6
[Meta.isDefEq] ✅️ Type (?u.16600 + 1) =?= Type (?u.16600 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.16600 + 1) =?= Type (?u.16600 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16600} =?= AddMonoidWithOne Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16600} =?= NatCast Ordinal.{?u.16600}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 4 =?= OfNat ℕ 4
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (4 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16629 =?= instOfNatAtLeastTwo ▶
Termination.lean:573:35
simp made no progress
Termination.lean:573:35
[Meta.isDefEq] ✅️ ?x > ?y =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= 3 < 6 ▶
Termination.lean:574:4
[Meta.isDefEq] ✅️ 6 ≤ mu n.delta + 6 =?= 6 ≤ mu n.delta + 6
[Meta.isDefEq] ✅️ 3 < mu n.delta + 6 =?= 3 < mu n.delta + 6
[Meta.isDefEq] ✅️ 3 < mu n.delta + 6 =?= 3 < mu n.delta + 6
Termination.lean:574:12
[Meta.isDefEq] ✅️ Ordinal.{?u.16797} =?= ?m.16799 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16797} 6 =?= OfNat ?m.16804 ?m.16805 ▶
[Meta.isDefEq] ✅️ ?m.16801 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16797} =?= NatCast ?m.16811 ▶
[Meta.isDefEq] ✅️ ?m.16806 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16797} =?= AddMonoidWithOne Ordinal.{?u.16817} ▶
[Meta.isDefEq] ✅️ ?m.16812 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16812 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16806 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (?m.16820 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16807 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16807 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16797} 6 =?= OfNat Ordinal.{?u.16797} 6
[Meta.isDefEq] ✅️ Type (?u.16797 + 1) =?= Type (?u.16797 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.16797 + 1) =?= Type (?u.16797 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16797} =?= AddMonoidWithOne Ordinal.{?u.16797}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16797} =?= NatCast Ordinal.{?u.16797}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 4 =?= OfNat ℕ 4
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (4 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16800 =?= instOfNatAtLeastTwo ▶
Termination.lean:574:16
[Meta.isDefEq] ✅️ Sort ?u.16796 =?= Type (?u.16797 + 1)
Termination.lean:574:11
[Meta.isDefEq] ✅️ Ordinal.{?u.16797} =?= Ordinal.{?u.16797}
Termination.lean:574:31
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:574:37
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:574:30
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:574:11
[Meta.isDefEq] 💥️ Ordinal.{?u.16797} =?= Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16826} x Ordinal.{?u.16797} =?= CoeT ?m.16856 ?m.16857 ?m.16856 ▶
[Meta.isDefEq] ✅️ ?m.16850 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16826} x Ordinal.{?u.16797} =?= CoeT Ordinal.{?u.16826} x Ordinal.{?u.16826} ▶
[Meta.isDefEq] ✅️ Type (?u.16826 + 1) =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= ?m.16915 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ LE Ordinal.{?u.16826} =?= LE ?m.16920 ▶
[Meta.isDefEq] ✅️ ?m.16917 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16826} =?= Preorder ?m.16924 ▶
[Meta.isDefEq] ✅️ ?m.16921 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16826} =?= PartialOrder Ordinal.{?u.16936} ▶
[Meta.isDefEq] ✅️ ?m.16925 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16925 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16921 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.16826} =?= LE Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Type (?u.16826 + 1) =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ Type (?u.16826 + 1) =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16826} =?= PartialOrder Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16826} =?= Preorder Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ ?m.16916 =?= partialOrder.toLE ▶
Termination.lean:574:27
[Meta.isDefEq] ✅️ Type ?u.16867 =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ Type ?u.16868 =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.16869) =?= Type (?u.16826 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16826} Ordinal.{?u.16826} ?m.16870 =?= HAdd ?m.16873 ?m.16873 ?m.16873 ▶
[Meta.isDefEq] ✅️ ?m.16871 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16826} =?= Add Ordinal.{?u.16887} ▶
[Meta.isDefEq] ✅️ ?m.16874 =?= add ▶
[Meta.isDefEq] ✅️ ?m.16874 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16826} Ordinal.{?u.16826}
Ordinal.{?u.16826} =?= HAdd Ordinal.{?u.16826} Ordinal.{?u.16826} Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Type (?u.16826 + 1) =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16826} =?= Add Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= ?m.16828 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= ?m.16890 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16826} =?= ?m.16891 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16826} Ordinal.{?u.16826} ?m.16894 =?= HAdd ?m.16897 ?m.16897 ?m.16897 ▶
[Meta.isDefEq] ✅️ ?m.16895 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16826} =?= Add Ordinal.{?u.16908} ▶
[Meta.isDefEq] ✅️ ?m.16898 =?= add ▶
[Meta.isDefEq] ✅️ ?m.16898 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16826} Ordinal.{?u.16826} ?m.16892 =?= HAdd Ordinal.{?u.16826} Ordinal.{?u.16826} Ordinal.{?u.16826} ▶
[Meta.isDefEq] ✅️ Type (?u.16826 + 1) =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16826} =?= Add Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ ?m.16893 =?= instHAdd ▶
Termination.lean:574:42
[Meta.isDefEq] 💥️ OfNat ?m.16828 6 =?= OfNat ℕ+ ?m.16837 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16828 6 =?= OfNat ℕ+ ?m.16847 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16826} 6 =?= OfNat ?m.16943 ?m.16944 ▶
[Meta.isDefEq] ✅️ ?m.16940 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16826} =?= NatCast ?m.16950 ▶
[Meta.isDefEq] ✅️ ?m.16945 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16826} =?= AddMonoidWithOne Ordinal.{?u.16956} ▶
[Meta.isDefEq] ✅️ ?m.16951 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16951 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.16945 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (?m.16959 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16946 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16946 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16826} 6 =?= OfNat Ordinal.{?u.16826} 6
[Meta.isDefEq] ✅️ Type (?u.16826 + 1) =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.16826 + 1) =?= Type (?u.16826 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16826} =?= AddMonoidWithOne Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16826} =?= NatCast Ordinal.{?u.16826}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 4 =?= OfNat ℕ 4
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (4 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.16830 =?= instOfNatAtLeastTwo ▶
Termination.lean:575:14
[Meta.isDefEq] ✅️ Ordinal.{?u.16970} =?= ?m.16972 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16970} 0 =?= OfNat ?m.16978 0 ▶
[Meta.isDefEq] ✅️ ?m.16974 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.16970} =?= Zero Ordinal.{?u.16987} ▶
[Meta.isDefEq] ✅️ ?m.16979 =?= zero ▶
[Meta.isDefEq] ✅️ ?m.16979 =?= zero ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16970} 0 =?= OfNat Ordinal.{?u.16970} 0
[Meta.isDefEq] ✅️ Type (?u.16970 + 1) =?= Type (?u.16970 + 1)
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.16970} =?= Zero Ordinal.{?u.16970}
[Meta.isDefEq] ✅️ ?m.16973 =?= Zero.toOfNat0 ▶
Termination.lean:575:18
[Meta.isDefEq] ✅️ Sort ?u.16969 =?= Type (?u.16970 + 1)
Termination.lean:575:13
[Meta.isDefEq] ✅️ Ordinal.{?u.16970} =?= Ordinal.{?u.16970}
Termination.lean:575:33
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:575:39
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:575:13
[Meta.isDefEq] 💥️ Ordinal.{?u.16970} =?= Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16992} x Ordinal.{?u.16970} =?= CoeT ?m.17000 ?m.17001 ?m.17000 ▶
[Meta.isDefEq] ✅️ ?m.16994 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16992} x Ordinal.{?u.16970} =?= CoeT Ordinal.{?u.16992} x Ordinal.{?u.16992} ▶
[Meta.isDefEq] ✅️ Type (?u.16992 + 1) =?= Type (?u.16992 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.16992} =?= Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Ordinal.{?u.16992} =?= Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Ordinal.{?u.16992} =?= Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Ordinal.{?u.16992} =?= Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Ordinal.{?u.16992} =?= ?m.17011 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16992} =?= Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ LE Ordinal.{?u.16992} =?= LE ?m.17016 ▶
[Meta.isDefEq] ✅️ ?m.17013 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16992} =?= Preorder ?m.17020 ▶
[Meta.isDefEq] ✅️ ?m.17017 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16992} =?= PartialOrder Ordinal.{?u.17032} ▶
[Meta.isDefEq] ✅️ ?m.17021 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17021 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17017 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.16992} =?= LE Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Type (?u.16992 + 1) =?= Type (?u.16992 + 1)
[Meta.isDefEq] ✅️ Type (?u.16992 + 1) =?= Type (?u.16992 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16992} =?= PartialOrder Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16992} =?= Preorder Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ ?m.17012 =?= partialOrder.toLE ▶
Termination.lean:575:32
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:575:6
[Meta.isDefEq] ✅️ 6 ≤ mu n.delta + 6 =?= 6 ≤ mu n.delta + 6
[Meta.isDefEq] ✅️ 6 ≤ mu n.delta + 6 =?= 6 ≤ mu n.delta + 6 ▶
Termination.lean:575:45
[Meta.isDefEq] 💥️ AddZeroClass ?m.17067 =?= AddZeroClass ((i : ?m.17087) → ?m.17088 i) ▶
[Meta.isDefEq] 💥️ LE ?m.17067 =?= LE ((i : ?m.17127) → ?m.17128 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.17067 =?= CanonicallyOrderedAdd (WithTop ?m.17138) ▶
[Meta.isDefEq] ✅️ 0 ≤ mu n.delta =?= 0 ≤ ?m.17071 ▶
[Meta.isDefEq] ✅️ AddZeroClass Ordinal.{?u.16992} =?= AddZeroClass ?m.17177 ▶
[Meta.isDefEq] ✅️ ?m.17175 =?= AddMonoid.toAddZeroClass ▶
[Meta.isDefEq] ✅️ AddMonoid Ordinal.{?u.16992} =?= AddMonoid ?m.17184 ▶
[Meta.isDefEq] ✅️ ?m.17178 =?= AddMonoidWithOne.toAddMonoid ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16992} =?= AddMonoidWithOne Ordinal.{?u.17188} ▶
[Meta.isDefEq] ✅️ ?m.17185 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.17185 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.17178 =?= addMonoidWithOne.toAddMonoid ▶
[Meta.isDefEq] ✅️ AddZeroClass Ordinal.{?u.16992} =?= AddZeroClass Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Type (?u.16992 + 1) =?= Type (?u.16992 + 1)
[Meta.isDefEq] ✅️ Type (?u.16992 + 1) =?= Type (?u.16992 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16992} =?= AddMonoidWithOne Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ AddMonoid Ordinal.{?u.16992} =?= AddMonoid Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ addMonoidWithOne.toAddZeroClass =?= addMonoidWithOne.toAddZeroClass
[Meta.isDefEq] ✅️ LE Ordinal.{?u.16992} =?= LE Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ✅️ CanonicallyOrderedAdd Ordinal.{?u.16992} =?= CanonicallyOrderedAdd Ordinal.{?u.17190} ▶
[Meta.isDefEq] ✅️ ?m.17189 =?= canonicallyOrderedAdd ▶
[Meta.isDefEq] ✅️ CanonicallyOrderedAdd Ordinal.{?u.16992} =?= CanonicallyOrderedAdd Ordinal.{?u.16992} ▶
[Meta.isDefEq] ✅️ ?m.17070 =?= canonicallyOrderedAdd ▶
[Meta.isDefEq] ✅️ 0 ≤ mu n.delta =?= 0 ≤ mu n.delta ▶
Termination.lean:575:53
[Meta.isDefEq] ✅️ ?m.17067 =?= ?m.17067
Termination.lean:576:35
[Meta.isDefEq] ✅️ ?m.21826 ≤ ?m.21827 =?= 0 ≤ mu n.delta ▶
[Meta.isDefEq] ✅️ 0 ≤ mu n.delta =?= 0 ≤ mu n.delta ▶
Termination.lean:576:6
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ Subsingleton Ordinal.{?u.16826} =?= Subsingleton ?m.17420 ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.16826} =?= Subsingleton ?m.17422 ▶
[Meta.isDefEq] ✅️ ?m.17417 =?= Unique.instSubsingleton ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.16826} =?= Subsingleton ?m.17424 ▶
[Meta.isDefEq] ✅️ ?m.17417 =?= IsEmpty.instSubsingleton ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b + ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.17604} Ordinal.{?u.17604} (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.17603} Ordinal.{?u.17603} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.17597 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.16826} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.17809 ?m.17809 (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.17802 =?= IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT Ordinal.{?u.16826} ▶
[Meta.isDefEq] ✅️ IsRightCancelAdd Ordinal.{?u.16826} =?= IsRightCancelAdd ?m.17848 ▶
[Meta.isDefEq] ✅️ ?m.17811 =?= IsCancelAdd.toIsRightCancelAdd ▶
[Meta.isDefEq] ❌️ IsCancelAdd Ordinal.{?u.16826} =?= IsCancelAdd ?m.17857 ▶
[Meta.isDefEq] ❌️ IsCancelAdd Ordinal.{?u.16826} =?= IsCancelAdd ?m.18353 ▶
[Meta.isDefEq] ❌️ IsRightCancelAdd Ordinal.{?u.16826} =?= IsRightCancelAdd ?m.18615 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.18771 ?m.18771 (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.19051 ?m.19051 (Function.swap fun x1 x2 => x1 + x2) ?m.19052 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.19868 ?m.19868 (Function.swap fun x1 x2 => x1 _ x2) ?m.19869 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.19968 ?m.19968 (Function.swap fun x1 x2 => x1 + x2) ?m.19969 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16826} Ordinal.{?u.16826} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.21230 ?m.21230 (Function.swap fun x1 x2 => x1 _ x2) ?m.21231 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?b + ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= 6 ≤ mu n.delta + 6 ▶
[Meta.Tactic.simp.rewrite] ge*iff_le:1000:
6 ≤ mu n.delta + 6
==>
6 ≤ mu n.delta + 6
[Meta.isDefEq] ✅️ 0 + ?a =?= 0 + 6 ▶
[Meta.Tactic.simp.rewrite] zero_add:1000:
0 + 6
==>
6
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ Subsingleton Ordinal.{?u.16992} =?= Subsingleton ?m.22164 ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.16992} =?= Subsingleton ?m.22166 ▶
[Meta.isDefEq] ✅️ ?m.22161 =?= Unique.instSubsingleton ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.16992} =?= Subsingleton ?m.22168 ▶
[Meta.isDefEq] ✅️ ?m.22161 =?= IsEmpty.instSubsingleton ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b + ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.22315} Ordinal.{?u.22315} (Function.swap fun x1 x2 => x1 * x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.22314} Ordinal.{?u.22314} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.22308 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.16992} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.22468 ?m.22468 (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.22461 =?= IsRightCancelAdd.addRightReflectLE*of_addRightReflectLT Ordinal.{?u.16992} ▶
[Meta.isDefEq] ✅️ IsRightCancelAdd Ordinal.{?u.16992} =?= IsRightCancelAdd ?m.22508 ▶
[Meta.isDefEq] ✅️ ?m.22470 =?= IsCancelAdd.toIsRightCancelAdd ▶
[Meta.isDefEq] ❌️ IsCancelAdd Ordinal.{?u.16992} =?= IsCancelAdd ?m.22517 ▶
[Meta.isDefEq] ❌️ IsCancelAdd Ordinal.{?u.16992} =?= IsCancelAdd ?m.23013 ▶
[Meta.isDefEq] ❌️ IsRightCancelAdd Ordinal.{?u.16992} =?= IsRightCancelAdd ?m.23275 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.23431 ?m.23431 (Function.swap fun x1 x2 => x1 * x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.23711 ?m.23711 (Function.swap fun x1 x2 => x1 + x2) ?m.23712 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.24528 ?m.24528 (Function.swap fun x1 x2 => x1 _ x2) ?m.24529 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.24628 ?m.24628 (Function.swap fun x1 x2 => x1 + x2) ?m.24629 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.25890 ?m.25890 (Function.swap fun x1 x2 => x1 _ x2) ?m.25891 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?b + ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b + ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.16992} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddRightMono ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?b + ?a =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ 6 ≤ mu n.delta + 6 =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ 6 ≤ mu n.delta + 6 =?= 6 ≤ mu n.delta + 6 ▶
Termination.lean:576:18
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16992} =?= Add Ordinal.{?u.21886} ▶
[Meta.isDefEq] ✅️ ?m.21879 =?= add ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16992} =?= Add Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ ?m.21823 =?= add ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.16992} =?= LE Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.21896} Ordinal.{?u.21896} (Function.swap fun x1 x2 => x1 \* x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.21895} Ordinal.{?u.21895} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.21889 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.16992} Ordinal.{?u.16992} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.16992} ▶
[Meta.isDefEq] ✅️ ?m.21825 =?= instAddRightMono ▶
Termination.lean:576:40
[Meta.isDefEq] ✅️ Ordinal.{?u.16992} =?= ?m.21857 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16992} 6 =?= OfNat ?m.21862 ?m.21863 ▶
[Meta.isDefEq] ✅️ ?m.21859 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16992} =?= NatCast ?m.21869 ▶
[Meta.isDefEq] ✅️ ?m.21864 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16992} =?= AddMonoidWithOne Ordinal.{?u.21875} ▶
[Meta.isDefEq] ✅️ ?m.21870 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.21870 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.21864 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (?m.21876 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.21865 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.21865 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16992} 6 =?= OfNat Ordinal.{?u.16992} 6
[Meta.isDefEq] ✅️ Type (?u.16992 + 1) =?= Type (?u.16992 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.16992 + 1) =?= Type (?u.16992 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.16992} =?= AddMonoidWithOne Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.16992} =?= NatCast Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 4 =?= OfNat ℕ 4
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (4 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.21858 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16992} =?= Ordinal.{?u.16992}
Termination.lean:577:26
[Meta.isDefEq] 💥️ OfNat ?m.27753 3 =?= OfNat ℕ+ ?m.27762 ▶
[Meta.isDefEq] 💥️ OfNat ?m.27753 3 =?= OfNat ℕ+ ?m.27772 ▶
[Meta.isDefEq] 💥️ OfNat ?m.27753 3 =?= OfNat ℕ+ ?m.27794 ▶
[Meta.isDefEq] 💥️ OfNat ?m.27804 3 =?= OfNat ℕ+ ?m.27859 ▶
[Meta.isDefEq] 💥️ OfNat ?m.27804 3 =?= OfNat ℕ+ ?m.27900 ▶
[Meta.isDefEq] ✅️ ?m.27755 =?= instOfNatNat ?n ▶
Termination.lean:577:26
[Meta.isDefEq] ✅️ ?m.27753 =?= ?m.27804 ▶
[Meta.isDefEq] ✅️ ?m.27804 =?= ?m.27804
[Meta.isDefEq] 💥️ LT ?m.27804 =?= LT (Option ?m.27827) ▶
[Meta.isDefEq] ✅️ Sort ?u.27750 =?= Prop
[Meta.isDefEq] 💥️ LT ?m.27804 =?= LT (Option ?m.27851) ▶
[Meta.isDefEq] 💥️ LT ?m.27804 =?= LT (Option ?m.27892) ▶
[Meta.isDefEq] 💥️ LT ?m.27804 =?= LT (Option ?m.27931) ▶
[Meta.isDefEq] ✅️ LT ℕ =?= LT ℕ
[Meta.isDefEq] ✅️ ?m.27944 =?= instLTNat ▶
[Meta.isDefEq] ✅️ LT ℕ =?= LT ℕ
[Meta.isDefEq] ✅️ ?m.27805 =?= instLTNat ▶
Termination.lean:577:30
[Meta.isDefEq] 💥️ OfNat ?m.27775 6 =?= OfNat ℕ+ ?m.27784 ▶
[Meta.isDefEq] 💥️ OfNat ?m.27775 6 =?= OfNat ℕ+ ?m.27802 ▶
[Meta.isDefEq] ✅️ ?m.27775 =?= ?m.27753 ▶
[Meta.isDefEq] 💥️ OfNat ?m.27804 6 =?= OfNat ℕ+ ?m.27869 ▶
[Meta.isDefEq] 💥️ OfNat ?m.27804 6 =?= OfNat ℕ+ ?m.27908 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 6 =?= OfNat ℕ ?m.27939 ▶
[Meta.isDefEq] ✅️ ?m.27936 =?= instOfNatNat 6 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 6 =?= OfNat ℕ 6
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ?m.27777 =?= instOfNatNat 6 ▶
Termination.lean:577:25
tactic 'assumption' failed
n : Trace
this✝ : 3 < 6
this : 6 ≤ mu n.delta + 6
⊢ 3 < 6
Termination.lean:577:25
[Meta.isDefEq] ✅️ 3 < 6 =?= 3 < 6
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < ?m.27698 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] 💥️ CoeT (3 < 6) ?m.27948 (3 < ?m.27698) =?= CoeT ?m.28080 ?m.28081 ?m.28080 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] ❌️ CoeT (3 < 6) ?m.27948 (3 < 6) =?= CoeT ?m.28261 ?m.28262 ?m.28261 ▶
[Meta.isDefEq] ✅️ CoeT (3 < 6) ?m.27948 (3 < 6) =?= CoeT ?m.28282 ?m.28283 ?m.28284 ▶
[Meta.isDefEq] ✅️ ?m.28255 =?= instCoeTOfCoeDep ▶
[Meta.isDefEq] ✅️ CoeT (3 < 6) ?m.27948 (3 < 6) =?= CoeT ?m.28286 ?m.28288 ?m.28287 ▶
[Meta.isDefEq] ✅️ ?m.28255 =?= instCoeTOfCoeHTCT ▶
[Meta.isDefEq] ❌️ CoeHTCT (3 < 6) (3 < 6) =?= CoeHTCT ?m.28296 ?m.28296 ▶
[Meta.isDefEq] ✅️ CoeHTCT (3 < 6) (3 < 6) =?= CoeHTCT ?m.28311 ?m.28312 ▶
[Meta.isDefEq] ✅️ ?m.28289 =?= instCoeHTCTOfCoeHTC ▶
[Meta.isDefEq] ❌️ CoeHTC (3 < 6) (3 < 6) =?= CoeHTC ?m.28322 ?m.28322 ▶
[Meta.isDefEq] ✅️ CoeHTC (3 < 6) (3 < 6) =?= CoeHTC ?m.28337 ?m.28338 ▶
[Meta.isDefEq] ✅️ ?m.28313 =?= instCoeHTCOfCoeOTC ▶
[Meta.isDefEq] ❌️ CoeOTC (3 < 6) (3 < 6) =?= CoeOTC ?m.28348 ?m.28348 ▶
[Meta.isDefEq] ✅️ CoeOTC (3 < 6) (3 < 6) =?= CoeOTC ?m.28363 ?m.28364 ▶
[Meta.isDefEq] ✅️ ?m.28339 =?= instCoeOTCOfCoeTC ▶
[Meta.isDefEq] ❌️ CoeTC (3 < 6) (3 < 6) =?= CoeTC ?m.28374 ?m.28374 ▶
[Meta.isDefEq] ✅️ CoeTC (3 < 6) (3 < 6) =?= CoeTC ?m.28389 ?m.28390 ▶
[Meta.isDefEq] ✅️ ?m.28365 =?= instCoeTCOfCoe_1 ▶
[Meta.isDefEq] ✅️ CoeTC (3 < 6) (3 < 6) =?= CoeTC ?m.28396 ?m.28395 ▶
[Meta.isDefEq] ✅️ ?m.28365 =?= instCoeTCOfCoe ▶
[Meta.isDefEq] ✅️ CoeOTC (3 < 6) (3 < 6) =?= CoeOTC ?m.28399 ?m.28401 ▶
[Meta.isDefEq] ✅️ ?m.28339 =?= instCoeOTCOfCoeOut ▶
[Meta.isDefEq] ✅️ CoeOut (3 < 6) ?m.28400 =?= CoeOut ?m.28408 ?m.28409 ▶
[Meta.isDefEq] ✅️ ?m.28402 =?= instCoeOutOfCoeSort ▶
[Meta.isDefEq] ❌️ CoeSort (3 < 6) ?m.28409 =?= CoeSort ?m.28417 (Type ?u.28416) ▶
[Meta.isDefEq] ✅️ CoeOut (3 < 6) ?m.28400 =?= CoeOut ?m.28422 ?m.28423 ▶
[Meta.isDefEq] ✅️ ?m.28402 =?= instCoeOutOfCoeFun ▶
[Meta.isDefEq] ✅️ CoeFun (3 < 6) fun x => ?m.28423 =?= CoeFun ?m.28430 fun x => (a : ?m.28431) → ?m.28432 a ▶
[Meta.isDefEq] ✅️ ?m.28424 =?= DFunLike.hasCoeToFun ▶
[Meta.isDefEq] ✅️ DFunLike (3 < 6) ?m.28431 ?m.28432 =?= DFunLike ?m.28447 ?m.28448 fun x => ?m.28449 ▶
[Meta.isDefEq] ✅️ ?m.28433 =?= EquivLike.toFunLike ▶
[Meta.isDefEq] ✅️ CoeHTC (3 < 6) (3 < 6) =?= CoeHTC ?m.28458 ?m.28460 ▶
[Meta.isDefEq] ✅️ ?m.28313 =?= instCoeHTCOfCoeHeadOfCoeOTC ▶
[Meta.isDefEq] ✅️ CoeHTCT (3 < 6) (3 < 6) =?= CoeHTCT ?m.28465 ?m.28464 ▶
[Meta.isDefEq] ✅️ ?m.28289 =?= instCoeHTCTOfCoeTailOfCoeHTC ▶
[Meta.isDefEq] ❌️ CoeTail ?m.28463 (3 < 6) =?= CoeTail ℕ ?m.28472 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.28463 (3 < 6) =?= CoeTail ℤ ?m.28476 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.28463 (3 < 6) =?= CoeTail ℚ≥0 ?m.28478 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.28463 (3 < 6) =?= CoeTail ℚ ?m.28480 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= Trace ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] ❌️ CoeT (3 < 6) ⋯ (3 < 6) =?= CoeT ?m.29164 ?m.29165 ?m.29164 ▶
[Meta.isDefEq] ✅️ CoeT (3 < 6) ⋯ (3 < 6) =?= CoeT ?m.29188 ?m.29189 ?m.29190 ▶
[Meta.isDefEq] ✅️ ?m.29158 =?= instCoeTOfCoeDep ▶
[Meta.isDefEq] ✅️ CoeT (3 < 6) ⋯ (3 < 6) =?= CoeT ?m.29192 ?m.29194 ?m.29193 ▶
[Meta.isDefEq] ✅️ ?m.29158 =?= instCoeTOfCoeHTCT ▶
[Meta.isDefEq] ❌️ CoeHTCT (3 < 6) (3 < 6) =?= CoeHTCT ?m.29202 ?m.29202 ▶
[Meta.isDefEq] ✅️ CoeHTCT (3 < 6) (3 < 6) =?= CoeHTCT ?m.29217 ?m.29218 ▶
[Meta.isDefEq] ✅️ ?m.29195 =?= instCoeHTCTOfCoeHTC ▶
[Meta.isDefEq] ❌️ CoeHTC (3 < 6) (3 < 6) =?= CoeHTC ?m.29228 ?m.29228 ▶
[Meta.isDefEq] ✅️ CoeHTC (3 < 6) (3 < 6) =?= CoeHTC ?m.29243 ?m.29244 ▶
[Meta.isDefEq] ✅️ ?m.29219 =?= instCoeHTCOfCoeOTC ▶
[Meta.isDefEq] ❌️ CoeOTC (3 < 6) (3 < 6) =?= CoeOTC ?m.29254 ?m.29254 ▶
[Meta.isDefEq] ✅️ CoeOTC (3 < 6) (3 < 6) =?= CoeOTC ?m.29269 ?m.29270 ▶
[Meta.isDefEq] ✅️ ?m.29245 =?= instCoeOTCOfCoeTC ▶
[Meta.isDefEq] ❌️ CoeTC (3 < 6) (3 < 6) =?= CoeTC ?m.29280 ?m.29280 ▶
[Meta.isDefEq] ✅️ CoeTC (3 < 6) (3 < 6) =?= CoeTC ?m.29295 ?m.29296 ▶
[Meta.isDefEq] ✅️ ?m.29271 =?= instCoeTCOfCoe_1 ▶
[Meta.isDefEq] ✅️ CoeTC (3 < 6) (3 < 6) =?= CoeTC ?m.29302 ?m.29301 ▶
[Meta.isDefEq] ✅️ ?m.29271 =?= instCoeTCOfCoe ▶
[Meta.isDefEq] ✅️ CoeOTC (3 < 6) (3 < 6) =?= CoeOTC ?m.29305 ?m.29307 ▶
[Meta.isDefEq] ✅️ ?m.29245 =?= instCoeOTCOfCoeOut ▶
[Meta.isDefEq] ✅️ CoeOut (3 < 6) ?m.29306 =?= CoeOut ?m.29314 ?m.29315 ▶
[Meta.isDefEq] ✅️ ?m.29308 =?= instCoeOutOfCoeSort ▶
[Meta.isDefEq] ❌️ CoeSort (3 < 6) ?m.29315 =?= CoeSort ?m.29323 (Type ?u.29322) ▶
[Meta.isDefEq] ✅️ CoeOut (3 < 6) ?m.29306 =?= CoeOut ?m.29328 ?m.29329 ▶
[Meta.isDefEq] ✅️ ?m.29308 =?= instCoeOutOfCoeFun ▶
[Meta.isDefEq] ✅️ CoeFun (3 < 6) fun x => ?m.29329 =?= CoeFun ?m.29336 fun x => (a : ?m.29337) → ?m.29338 a ▶
[Meta.isDefEq] ✅️ ?m.29330 =?= DFunLike.hasCoeToFun ▶
[Meta.isDefEq] ✅️ DFunLike (3 < 6) ?m.29337 ?m.29338 =?= DFunLike ?m.29353 ?m.29354 fun x => ?m.29355 ▶
[Meta.isDefEq] ✅️ ?m.29339 =?= EquivLike.toFunLike ▶
[Meta.isDefEq] ✅️ CoeHTC (3 < 6) (3 < 6) =?= CoeHTC ?m.29364 ?m.29366 ▶
[Meta.isDefEq] ✅️ ?m.29219 =?= instCoeHTCOfCoeHeadOfCoeOTC ▶
[Meta.isDefEq] ✅️ CoeHTCT (3 < 6) (3 < 6) =?= CoeHTCT ?m.29371 ?m.29370 ▶
[Meta.isDefEq] ✅️ ?m.29195 =?= instCoeHTCTOfCoeTailOfCoeHTC ▶
[Meta.isDefEq] ❌️ CoeTail ?m.29369 (3 < 6) =?= CoeTail ℕ ?m.29378 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.29369 (3 < 6) =?= CoeTail ℤ ?m.29382 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.29369 (3 < 6) =?= CoeTail ℚ≥0 ?m.29384 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.29369 (3 < 6) =?= CoeTail ℚ ?m.29386 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] ❌️ 3 < 6 =?= 3 < 6 ▶
[Meta.isDefEq] ❌️ LT.lt 3 =?= LT.lt 3 ▶
[Meta.isDefEq] ❌️ @LT.lt =?= @LT.lt ▶
Termination.lean:577:10
[Meta.isDefEq] 💥️ Preorder ?m.27695 =?= Preorder ((i : ?m.27729) → ?m.27730 i) ▶
[Meta.isDefEq] ✅️ 3 < mu n.delta + 6 =?= ?m.27697 < ?m.27699 ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16992} =?= Preorder ?m.28227 ▶
[Meta.isDefEq] ✅️ ?m.28225 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16992} =?= PartialOrder Ordinal.{?u.28237} ▶
[Meta.isDefEq] ✅️ ?m.28228 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.28228 =?= partialOrder ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16992} =?= Preorder Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ Type (?u.16992 + 1) =?= Type (?u.16992 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16992} =?= PartialOrder Ordinal.{?u.16992}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ✅️ 3 < mu n.delta + 6 =?= 3 < mu n.delta + 6 ▶
Termination.lean:577:33
[Meta.isDefEq] ✅️ ?m.27698 ≤ mu n.delta + 6 =?= 6 ≤ mu n.delta + 6 ▶
[Meta.isDefEq] ✅️ 6 ≤ mu n.delta + 6 =?= 6 ≤ mu n.delta + 6 ▶
Termination.lean:579:9
[Meta.isDefEq] ✅️ MetaSN.bigA n =?= ω ^ (MetaSN.mu n.delta + 6) ▶
[Meta.isDefEq] ✅️ MetaSN.bigA n =?= ω ^ (MetaSN.mu n.delta + 6) ▶
Termination.lean:579:40
[Meta.isDefEq] ✅️ ?m.29730 < ?m.29731 =?= 0 < ω ▶
[Meta.isDefEq] ✅️ 0 < ω =?= 0 < ω ▶
Termination.lean:579:21
Function expected at
opow_lt_opow_right omega0_pos
but this term has type
ω ^ 0 < ω ^ ω

Note: Expected a function because this term is being applied to the argument
three*lt_exp
Termination.lean:570:0
[diag] Diagnostics ▼
[reduction] unfolded declarations (max: 1029, num: 11): ▶
[reduction] unfolded instances (max: 4372, num: 18): ▶
[reduction] unfolded reducible declarations (max: 502, num: 4): ▶
[def_eq] heuristic for solving f a =?= f b (max: 247, num: 2): ▶
use set_option diagnostics.threshold <num> to control threshold for reporting counters
Termination.lean:570:51
[Meta.isDefEq] ✅️ ω ^ 3 < bigA n =?= ω ^ 3 < bigA n
Termination.lean:579:2
[Meta.Tactic.simp.rewrite] unfold bigA, bigA n ==> ω ^ (mu n.delta + 6)
[Meta.isDefEq] ✅️ ?x > ?y =?= ω ^ 3 < ω ^ (mu n.delta + 6) ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= ω ^ 3 < ω ^ (mu n.delta + 6) ▶
[Meta.isDefEq] ✅️ ?x > ?y =?= ω ^ 3 < ω ^ (mu n.delta + 6) ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= ω ^ 3 < ω ^ (mu n.delta + 6) ▶
[Meta.isDefEq] ✅️ ?x > ?y =?= ω ^ 3 < ω ^ (mu n.delta + 6) ▶
[Meta.Tactic.simp.rewrite] gt_iff_lt:1000:
ω ^ 3 < ω ^ (mu n.delta + 6)
==>
ω ^ 3 < ω ^ (mu n.delta + 6)
[Meta.isDefEq] ❌️ fun as => Array.filterMap some as =?= ?m.29788 ▶
[Meta.isDefEq] ✅️ ω ^ 3 < ω ^ (mu n.delta + 6) =?= ?m.29788 ▶
[Meta.isDefEq] ✅️ ω ^ 3 < ω ^ (mu n.delta + 6) =?= ω ^ 3 < ω ^ (mu n.delta + 6)
Termination.lean:579:21
[Meta.isDefEq] ✅️ CoeFun (ω ^ 0 < ω ^ ω) ?m.29753 =?= CoeFun ?m.29758 fun x => (a : ?m.29759) → ?m.29760 a ▶
[Meta.isDefEq] ✅️ ?m.29754 =?= DFunLike.hasCoeToFun ▶
[Meta.isDefEq] ✅️ DFunLike (ω ^ 0 < ω ^ ω) ?m.29759 ?m.29760 =?= DFunLike ?m.29776 ?m.29777 fun x => ?m.29778 ▶
[Meta.isDefEq] ✅️ ?m.29761 =?= EquivLike.toFunLike ▶
Termination.lean:581:23
[Meta.isDefEq] ✅️ Sort ?u.16423 =?= Type
[Meta.isDefEq] ✅️ Sort ?u.16425 =?= Type
Termination.lean:582:4
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= ?m.16748 ▶
[Meta.isDefEq] ✅️ ?m.16437 =?= ?m.16749 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16486} ?m.16749 ?m.16752 =?= HPow ?m.16757 ?m.16758 ?m.16757 ▶
[Meta.isDefEq] ✅️ ?m.16753 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16486} ?m.16749 =?= Pow Ordinal.{?u.16774} Ordinal.{?u.16774} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16486} ?m.16749 ?m.16868 =?= HPow ?m.16873 ?m.16874 ?m.16873 ▶
[Meta.isDefEq] ✅️ ?m.16869 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16486} ?m.16749 =?= Pow Ordinal.{?u.16887} Ordinal.{?u.16887} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16486} ?m.16749 ?m.16906 =?= HPow ?m.16911 ?m.16912 ?m.16911 ▶
[Meta.isDefEq] ✅️ ?m.16907 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16486} ?m.16749 =?= Pow Ordinal.{?u.16922} Ordinal.{?u.16922} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16486} ?m.16749 ?m.16938 =?= HPow ?m.16943 ?m.16944 ?m.16943 ▶
[Meta.isDefEq] ✅️ ?m.16939 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16486} ?m.16749 =?= Pow Ordinal.{?u.16954} Ordinal.{?u.16954} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.16486} ?m.16749 ?m.16970 =?= HPow ?m.16975 ?m.16976 ?m.16975 ▶
[Meta.isDefEq] ✅️ ?m.16971 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16486} ?m.16749 =?= Pow Ordinal.{?u.16986} Ordinal.{?u.16986} ▶
[Meta.isDefEq] ✅️ ?m.16751 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.16486} ?β =?= Pow Ordinal.{?u.17011} Ordinal.{?u.17011} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.16486} =?= Monoid Ordinal.{?u.17025} ▶
[Meta.isDefEq] ✅️ ?m.17019 =?= monoid ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.16486} =?= Monoid Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:582:13
[Meta.isDefEq] 💥️ OfNat ?m.16437 3 =?= OfNat ℕ+ ?m.16446 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16437 3 =?= OfNat ℕ+ ?m.16475 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16437 3 =?= OfNat ℕ+ ?m.16493 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16749 3 =?= OfNat ℕ+ ?m.16847 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16749 3 =?= OfNat ℕ+ ?m.16904 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16749 3 =?= OfNat ℕ+ ?m.16936 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16749 3 =?= OfNat ℕ+ ?m.16968 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ ?m.17031 ▶
[Meta.isDefEq] ✅️ ?m.17028 =?= instOfNatNat 3 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ 3
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ?m.16439 =?= instOfNatNat 3 ▶
Termination.lean:582:21
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:582:18
[Meta.isDefEq] ✅️ Type ?u.16725 =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Type ?u.16726 =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.16727) =?= Type (?u.16486 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16486} Ordinal.{?u.16486} ?m.16728 =?= HAdd ?m.16731 ?m.16731 ?m.16731 ▶
[Meta.isDefEq] ✅️ ?m.16729 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16486} =?= Add Ordinal.{?u.16745} ▶
[Meta.isDefEq] ✅️ ?m.16732 =?= add ▶
[Meta.isDefEq] ✅️ ?m.16732 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16486} Ordinal.{?u.16486}
Ordinal.{?u.16486} =?= HAdd Ordinal.{?u.16486} Ordinal.{?u.16486} Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16486} =?= Add Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= ?m.16455 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= ?m.16777 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= ?m.16778 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16486} Ordinal.{?u.16486} ?m.16781 =?= HAdd ?m.16784 ?m.16784 ?m.16784 ▶
[Meta.isDefEq] ✅️ ?m.16782 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16486} =?= Add Ordinal.{?u.16795} ▶
[Meta.isDefEq] ✅️ ?m.16785 =?= add ▶
[Meta.isDefEq] ✅️ ?m.16785 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.16486} Ordinal.{?u.16486} ?m.16779 =?= HAdd Ordinal.{?u.16486} Ordinal.{?u.16486} Ordinal.{?u.16486} ▶
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.16486} =?= Add Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ ?m.16780 =?= instHAdd ▶
Termination.lean:582:25
[Meta.isDefEq] 💥️ OfNat ?m.16455 1 =?= OfNat ℕ+ ?m.16465 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16455 1 =?= OfNat ℕ+ ?m.16484 ▶
[Meta.isDefEq] 💥️ OfNat ?m.16455 1 =?= OfNat ℕ+ ?m.16502 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16486} 1 =?= OfNat ?m.16855 1 ▶
[Meta.isDefEq] ✅️ ?m.16851 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.16486} =?= One Ordinal.{?u.16863} ▶
[Meta.isDefEq] ✅️ ?m.16856 =?= one ▶
[Meta.isDefEq] ✅️ ?m.16856 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.16486} 1 =?= OfNat Ordinal.{?u.16486} 1
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.16486} =?= One Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ ?m.16457 =?= One.toOfNat1 ▶
Termination.lean:582:4
[Meta.isDefEq] ✅️ Type ?u.16540 =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Type ?u.16541 =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.16542) =?= Type (?u.16486 + 1) ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.16486} Ordinal.{?u.16486} ?m.16543 =?= HMul ?m.16546 ?m.16546 ?m.16546 ▶
[Meta.isDefEq] ✅️ ?m.16544 =?= instHMul ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.16486} =?= Mul ?m.16560 ▶
[Meta.isDefEq] ✅️ ?m.16547 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.16486} =?= Distrib ?m.16565 ▶
[Meta.isDefEq] ✅️ ?m.16561 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.16486} =?= NonUnitalNonAssocSemiring ?m.16573 ▶
[Meta.isDefEq] ✅️ ?m.16566 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.16486} =?= NonUnitalNonAssocCommSemiring ?m.16578 ▶
[Meta.isDefEq] ✅️ ?m.16574 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.16486} =?= NonUnitalNonAssocCommRing ?m.16583 ▶
[Meta.isDefEq] ✅️ ?m.16579 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.16486} =?= NonUnitalCommRing ?m.16588 ▶
[Meta.isDefEq] ✅️ ?m.16584 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.16486} =?= CommRing ?m.16593 ▶
[Meta.isDefEq] ✅️ ?m.16589 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.16486} =?= NonUnitalNonAssocSemiring ?m.16597 ▶
[Meta.isDefEq] ✅️ ?m.16566 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.16486} =?= NonUnitalNonAssocRing ?m.16602 ▶
[Meta.isDefEq] ✅️ ?m.16598 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.16486} =?= NonUnitalNonAssocRing ?m.16606 ▶
[Meta.isDefEq] ✅️ ?m.16598 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.16486} =?= NonAssocRing ?m.16609 ▶
[Meta.isDefEq] ✅️ ?m.16607 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.16486} =?= Ring ?m.16615 ▶
[Meta.isDefEq] ✅️ ?m.16610 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.16486} =?= DivisionRing ?m.16620 ▶
[Meta.isDefEq] ✅️ ?m.16616 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.16486} =?= Ring ?m.16624 ▶
[Meta.isDefEq] ✅️ ?m.16610 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.16486} =?= NonUnitalNonAssocRing ?m.16626 ▶
[Meta.isDefEq] ✅️ ?m.16598 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.16486} =?= NonUnitalRing ?m.16630 ▶
[Meta.isDefEq] ✅️ ?m.16627 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.16486} =?= NonUnitalRing ?m.16634 ▶
[Meta.isDefEq] ✅️ ?m.16627 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.16486} =?= NonUnitalNonAssocSemiring ?m.16636 ▶
[Meta.isDefEq] ✅️ ?m.16566 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.16486} =?= NonAssocSemiring ?m.16640 ▶
[Meta.isDefEq] ✅️ ?m.16637 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.16486} =?= Semiring ?m.16647 ▶
[Meta.isDefEq] ✅️ ?m.16641 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.16486} =?= DivisionSemiring ?m.16653 ▶
[Meta.isDefEq] ✅️ ?m.16648 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.16486} =?= Semifield ?m.16658 ▶
[Meta.isDefEq] ✅️ ?m.16654 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.16486} =?= DivisionSemiring ?m.16662 ▶
[Meta.isDefEq] ✅️ ?m.16648 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.16486} =?= Semiring ?m.16664 ▶
[Meta.isDefEq] ✅️ ?m.16641 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.16486} =?= CommSemiring ?m.16668 ▶
[Meta.isDefEq] ✅️ ?m.16665 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.16486} =?= CommSemiring ?m.16672 ▶
[Meta.isDefEq] ✅️ ?m.16665 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.16486} =?= Semiring ?m.16674 ▶
[Meta.isDefEq] ✅️ ?m.16641 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.16486} =?= NonAssocSemiring ?m.16676 ▶
[Meta.isDefEq] ✅️ ?m.16637 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.16486} =?= NonUnitalNonAssocSemiring ?m.16678 ▶
[Meta.isDefEq] ✅️ ?m.16566 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.16486} =?= NonUnitalSemiring ?m.16683 ▶
[Meta.isDefEq] ✅️ ?m.16679 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.16486} =?= NonUnitalCommSemiring ?m.16689 ▶
[Meta.isDefEq] ✅️ ?m.16684 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.16486} =?= NonUnitalCommSemiring ?m.16693 ▶
[Meta.isDefEq] ✅️ ?m.16684 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.16486} =?= NonUnitalSemiring ?m.16695 ▶
[Meta.isDefEq] ✅️ ?m.16679 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.16486} =?= NonUnitalSemiring ?m.16697 ▶
[Meta.isDefEq] ✅️ ?m.16679 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.16486} =?= Mul ?m.16699 ▶
[Meta.isDefEq] ✅️ ?m.16547 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.16486} =?= MulZeroClass ?m.16704 ▶
[Meta.isDefEq] ✅️ ?m.16700 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.16486} =?= MulZeroClass ?m.16708 ▶
[Meta.isDefEq] ✅️ ?m.16700 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.16486} =?= MulZeroOneClass ?m.16712 ▶
[Meta.isDefEq] ✅️ ?m.16709 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.16486} =?= MulZeroOneClass ?m.16716 ▶
[Meta.isDefEq] ✅️ ?m.16709 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.16486} =?= MonoidWithZero Ordinal.{?u.16722} ▶
[Meta.isDefEq] ✅️ ?m.16717 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.16717 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.16709 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.16700 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ ?m.16547 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.16486} Ordinal.{?u.16486}
Ordinal.{?u.16486} =?= HMul Ordinal.{?u.16486} Ordinal.{?u.16486} Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.16486} =?= MonoidWithZero Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.16486} =?= MulZeroOneClass Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.16486} =?= MulZeroClass Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.16486} =?= Mul Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ ?m.16750 =?= ?m.16802 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= ?m.16803 ▶
[Meta.isDefEq] 💥️ HMul ?m.16802 Ordinal.{?u.16486} ?m.16806 =?= HMul ?m.16811 ?m.16811 ?m.16811 ▶
[Meta.isDefEq] 💥️ HMul ?m.16802 Ordinal.{?u.16486} ?m.16888 =?= HMul ?m.16893 ?m.16893 ?m.16893 ▶
[Meta.isDefEq] 💥️ HMul ?m.16802 Ordinal.{?u.16486} ?m.16923 =?= HMul ?m.16928 ?m.16928 ?m.16928 ▶
[Meta.isDefEq] 💥️ HMul ?m.16802 Ordinal.{?u.16486} ?m.16955 =?= HMul ?m.16960 ?m.16960 ?m.16960 ▶
[Meta.isDefEq] 💥️ HMul ?m.16802 Ordinal.{?u.16486} ?m.16987 =?= HMul ?m.16992 ?m.16992 ?m.16992 ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.16486} Ordinal.{?u.16486}
Ordinal.{?u.16486} =?= HMul Ordinal.{?u.16486} Ordinal.{?u.16486} Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ ?m.16805 =?= instHMul ▶
Termination.lean:582:4
[Meta.isDefEq] 💥️ Ordinal.{?u.16435} =?= Ordinal.{?u.16453}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16453} x Ordinal.{?u.16435} =?= CoeT ?m.16511 ?m.16512 ?m.16511 ▶
[Meta.isDefEq] ✅️ ?m.16505 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16453} x Ordinal.{?u.16435} =?= CoeT Ordinal.{?u.16453} x Ordinal.{?u.16453} ▶
[Meta.isDefEq] ✅️ Type (?u.16453 + 1) =?= Type (?u.16453 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.16453} =?= Ordinal.{?u.16453}
[Meta.isDefEq] ✅️ Ordinal.{?u.16453} =?= Ordinal.{?u.16453}
[Meta.isDefEq] 💥️ Ordinal.{?u.16453} =?= Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16486} x Ordinal.{?u.16453} =?= CoeT ?m.16529 ?m.16530 ?m.16529 ▶
[Meta.isDefEq] ✅️ ?m.16523 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.16486} x Ordinal.{?u.16453} =?= CoeT Ordinal.{?u.16486} x Ordinal.{?u.16486} ▶
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ ?m.16804 =?= ?m.16816 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.16486} =?= ?m.16816 ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.16486} =?= LT ?m.16821 ▶
[Meta.isDefEq] ✅️ ?m.16818 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16486} =?= Preorder ?m.16825 ▶
[Meta.isDefEq] ✅️ ?m.16822 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16486} =?= PartialOrder Ordinal.{?u.16837} ▶
[Meta.isDefEq] ✅️ ?m.16826 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16826 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.16822 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.16486} =?= LT Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ Type (?u.16486 + 1) =?= Type (?u.16486 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.16486} =?= PartialOrder Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.16486} =?= Preorder Ordinal.{?u.16486}
[Meta.isDefEq] ✅️ ?m.16817 =?= partialOrder.toLT ▶
Termination.lean:582:35
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:583:2
[Meta.isDefEq] ✅️ ω ^ 3 * (mu s + 1) < bigA n =?= ω ^ 3 _ (mu s + 1) < bigA n
[Meta.isDefEq] ✅️ ω ^ 3 _ (mu s + 1) < bigA n =?= ω ^ 3 _ (mu s + 1) < bigA n ▶
Termination.lean:583:18
[Meta.isDefEq] ✅️ ?m.17047 =?= ω ^ 3 < bigA n ▶
[Meta.isDefEq] ✅️ ω ^ 3 < bigA n =?= ω ^ 3 < bigA n
Termination.lean:583:26
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:584:2
[Meta.isDefEq] ✅️ 0 < mu s + 1 =?= 0 < mu s + 1
[Meta.isDefEq] ✅️ ω ^ 3 _ (mu s + 1) < bigA n =?= ω ^ 3 _ (mu s + 1) < bigA n
[Meta.isDefEq] ✅️ ω ^ 3 _ (mu s + 1) < bigA n =?= ω ^ 3 _ (mu s + 1) < bigA n
Termination.lean:584:14
[Meta.isDefEq] ✅️ Ordinal.{?u.17148} =?= ?m.17150 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17148} 0 =?= OfNat ?m.17156 0 ▶
[Meta.isDefEq] ✅️ ?m.17152 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.17148} =?= Zero Ordinal.{?u.17165} ▶
[Meta.isDefEq] ✅️ ?m.17157 =?= zero ▶
[Meta.isDefEq] ✅️ ?m.17157 =?= zero ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17148} 0 =?= OfNat Ordinal.{?u.17148} 0
[Meta.isDefEq] ✅️ Type (?u.17148 + 1) =?= Type (?u.17148 + 1)
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.17148} =?= Zero Ordinal.{?u.17148}
[Meta.isDefEq] ✅️ ?m.17151 =?= Zero.toOfNat0 ▶
Termination.lean:584:18
[Meta.isDefEq] ✅️ Sort ?u.17147 =?= Type (?u.17148 + 1)
Termination.lean:584:13
[Meta.isDefEq] ✅️ Ordinal.{?u.17148} =?= Ordinal.{?u.17148}
Termination.lean:584:32
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:584:13
[Meta.isDefEq] 💥️ Ordinal.{?u.17148} =?= Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17173} x Ordinal.{?u.17148} =?= CoeT ?m.17205 ?m.17206 ?m.17205 ▶
[Meta.isDefEq] ✅️ ?m.17199 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17173} x Ordinal.{?u.17148} =?= CoeT Ordinal.{?u.17173} x Ordinal.{?u.17173} ▶
[Meta.isDefEq] ✅️ Type (?u.17173 + 1) =?= Type (?u.17173 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= ?m.17264 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17173} =?= LT ?m.17269 ▶
[Meta.isDefEq] ✅️ ?m.17266 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17173} =?= Preorder ?m.17273 ▶
[Meta.isDefEq] ✅️ ?m.17270 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17173} =?= PartialOrder Ordinal.{?u.17285} ▶
[Meta.isDefEq] ✅️ ?m.17274 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17274 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17270 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17173} =?= LT Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ Type (?u.17173 + 1) =?= Type (?u.17173 + 1)
[Meta.isDefEq] ✅️ Type (?u.17173 + 1) =?= Type (?u.17173 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17173} =?= PartialOrder Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17173} =?= Preorder Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ ?m.17265 =?= partialOrder.toLT ▶
Termination.lean:584:29
[Meta.isDefEq] ✅️ Type ?u.17216 =?= Type (?u.17173 + 1)
[Meta.isDefEq] ✅️ Type ?u.17217 =?= Type (?u.17173 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.17218) =?= Type (?u.17173 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17173} Ordinal.{?u.17173} ?m.17219 =?= HAdd ?m.17222 ?m.17222 ?m.17222 ▶
[Meta.isDefEq] ✅️ ?m.17220 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17173} =?= Add Ordinal.{?u.17236} ▶
[Meta.isDefEq] ✅️ ?m.17223 =?= add ▶
[Meta.isDefEq] ✅️ ?m.17223 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17173} Ordinal.{?u.17173}
Ordinal.{?u.17173} =?= HAdd Ordinal.{?u.17173} Ordinal.{?u.17173} Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ Type (?u.17173 + 1) =?= Type (?u.17173 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17173} =?= Add Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= ?m.17175 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= ?m.17239 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17173} =?= ?m.17240 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17173} Ordinal.{?u.17173} ?m.17243 =?= HAdd ?m.17246 ?m.17246 ?m.17246 ▶
[Meta.isDefEq] ✅️ ?m.17244 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17173} =?= Add Ordinal.{?u.17257} ▶
[Meta.isDefEq] ✅️ ?m.17247 =?= add ▶
[Meta.isDefEq] ✅️ ?m.17247 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17173} Ordinal.{?u.17173} ?m.17241 =?= HAdd Ordinal.{?u.17173} Ordinal.{?u.17173} Ordinal.{?u.17173} ▶
[Meta.isDefEq] ✅️ Type (?u.17173 + 1) =?= Type (?u.17173 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17173} =?= Add Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ ?m.17242 =?= instHAdd ▶
Termination.lean:584:36
[Meta.isDefEq] 💥️ OfNat ?m.17175 1 =?= OfNat ℕ+ ?m.17185 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17175 1 =?= OfNat ℕ+ ?m.17196 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17173} 1 =?= OfNat ?m.17293 1 ▶
[Meta.isDefEq] ✅️ ?m.17289 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.17173} =?= One Ordinal.{?u.17301} ▶
[Meta.isDefEq] ✅️ ?m.17294 =?= one ▶
[Meta.isDefEq] ✅️ ?m.17294 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17173} 1 =?= OfNat Ordinal.{?u.17173} 1
[Meta.isDefEq] ✅️ Type (?u.17173 + 1) =?= Type (?u.17173 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.17173} =?= One Ordinal.{?u.17173}
[Meta.isDefEq] ✅️ ?m.17177 =?= One.toOfNat1 ▶
Termination.lean:585:4
[Meta.isDefEq] ✅️ 0 < 1 =?= 0 < 1
[Meta.isDefEq] ✅️ 0 < mu s + 1 =?= 0 < mu s + 1
[Meta.isDefEq] ✅️ 0 < mu s + 1 =?= 0 < mu s + 1 ▶
Termination.lean:585:12
[Meta.isDefEq] ✅️ Ordinal.{?u.17314} =?= ?m.17316 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17314} 0 =?= OfNat ?m.17322 0 ▶
[Meta.isDefEq] ✅️ ?m.17318 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.17314} =?= Zero Ordinal.{?u.17331} ▶
[Meta.isDefEq] ✅️ ?m.17323 =?= zero ▶
[Meta.isDefEq] ✅️ ?m.17323 =?= zero ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17314} 0 =?= OfNat Ordinal.{?u.17314} 0
[Meta.isDefEq] ✅️ Type (?u.17314 + 1) =?= Type (?u.17314 + 1)
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.17314} =?= Zero Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ ?m.17317 =?= Zero.toOfNat0 ▶
Termination.lean:585:16
[Meta.isDefEq] ✅️ Sort ?u.17313 =?= Type (?u.17314 + 1)
Termination.lean:585:11
[Meta.isDefEq] ✅️ Ordinal.{?u.17314} =?= Ordinal.{?u.17314}
Termination.lean:585:11
[Meta.isDefEq] ✅️ Ordinal.{?u.17314} =?= Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ Ordinal.{?u.17314} =?= ?m.17337 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17314} =?= ?m.17360 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17314} =?= Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17314} =?= LT ?m.17365 ▶
[Meta.isDefEq] ✅️ ?m.17362 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17314} =?= Preorder ?m.17369 ▶
[Meta.isDefEq] ✅️ ?m.17366 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17314} =?= PartialOrder Ordinal.{?u.17381} ▶
[Meta.isDefEq] ✅️ ?m.17370 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17370 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17366 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17314} =?= LT Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ Type (?u.17314 + 1) =?= Type (?u.17314 + 1)
[Meta.isDefEq] ✅️ Type (?u.17314 + 1) =?= Type (?u.17314 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17314} =?= PartialOrder Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17314} =?= Preorder Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ ?m.17361 =?= partialOrder.toLT ▶
Termination.lean:585:27
[Meta.isDefEq] 💥️ OfNat ?m.17337 1 =?= OfNat ℕ+ ?m.17347 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17337 1 =?= OfNat ℕ+ ?m.17358 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17314} 1 =?= OfNat ?m.17389 1 ▶
[Meta.isDefEq] ✅️ ?m.17385 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.17314} =?= One Ordinal.{?u.17395} ▶
[Meta.isDefEq] ✅️ ?m.17390 =?= one ▶
[Meta.isDefEq] ✅️ ?m.17390 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17314} 1 =?= OfNat Ordinal.{?u.17314} 1
[Meta.isDefEq] ✅️ Type (?u.17314 + 1) =?= Type (?u.17314 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.17314} =?= One Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ ?m.17339 =?= One.toOfNat1 ▶
Termination.lean:585:35
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.17314} =?= AddMonoidWithOne Ordinal.{?u.17406} ▶
[Meta.isDefEq] ✅️ ?m.17403 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.17314} =?= AddMonoidWithOne Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ OfNat.ofNat ?m.17408 =?= 0 ▶
[Meta.isDefEq] ✅️ 0 =?= 0 ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.17314} =?= AddMonoidWithOne Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ OfNat.ofNat ?m.17420 =?= 1 ▶
[Meta.isDefEq] ✅️ 1 =?= 1 ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17314} =?= LT Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ LT.lt =?= LT.lt
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17314} =?= Semiring ?m.17430 ▶
[Meta.isDefEq] ✅️ ?m.17426 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.17314} =?= DivisionSemiring ?m.17435 ▶
[Meta.isDefEq] ✅️ ?m.17431 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.17314} =?= Semifield ?m.17440 ▶
[Meta.isDefEq] ✅️ ?m.17436 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.17314} =?= DivisionSemiring ?m.17444 ▶
[Meta.isDefEq] ✅️ ?m.17431 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.17314} =?= DivisionRing ?m.17447 ▶
[Meta.isDefEq] ✅️ ?m.17445 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17314} =?= Semiring ?m.17451 ▶
[Meta.isDefEq] ✅️ ?m.17426 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.17314} =?= CommSemiring ?m.17455 ▶
[Meta.isDefEq] ✅️ ?m.17452 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.17314} =?= CommSemiring ?m.17459 ▶
[Meta.isDefEq] ✅️ ?m.17452 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.17314} =?= CommRing ?m.17462 ▶
[Meta.isDefEq] ✅️ ?m.17460 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17314} =?= Semiring ?m.17466 ▶
[Meta.isDefEq] ✅️ ?m.17426 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.17314} =?= Ring ?m.17470 ▶
[Meta.isDefEq] ✅️ ?m.17467 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.17314} =?= Ring ?m.17474 ▶
[Meta.isDefEq] ✅️ ?m.17467 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ ?x > ?y =?= 0 < 1 ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ OfNat.ofNat ?n < 1 =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass Ordinal.{?u.17644} Ordinal.{?u.17644} (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.17641 =?= instAddLeftMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddLeftMono Ordinal.{?u.17314} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddLeftMono ▶
[Meta.isDefEq] ✅️ ZeroLEOneClass Ordinal.{?u.17314} =?= ZeroLEOneClass Ordinal.{?u.17778} ▶
[Meta.isDefEq] ✅️ ?m.17772 =?= instZeroLEOneClass ▶
[Meta.isDefEq] ✅️ ZeroLEOneClass Ordinal.{?u.17314} =?= ZeroLEOneClass Ordinal.{?u.17314} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instZeroLEOneClass ▶
[Meta.isDefEq] ✅️ CharZero Ordinal.{?u.17314} =?= CharZero Ordinal.{?u.17805} ▶
[Meta.isDefEq] ✅️ ?m.17803 =?= instCharZero ▶
[Meta.isDefEq] ✅️ CharZero Ordinal.{?u.17314} =?= CharZero Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ ?inst✝ =?= instCharZero ▶
[Meta.isDefEq] ❌️ Nat.AtLeastTwo 0 =?= (?m.17811 + 2).AtLeastTwo ▶
[Meta.isDefEq] ❌️ 0 < OfNat.ofNat ?n =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ 0 < 1 =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ ZeroLEOneClass Ordinal.{?u.17314} =?= ZeroLEOneClass Ordinal.{?u.17988} ▶
[Meta.isDefEq] ✅️ ?m.17982 =?= instZeroLEOneClass ▶
[Meta.isDefEq] ✅️ ZeroLEOneClass Ordinal.{?u.17314} =?= ZeroLEOneClass Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ ?inst✝ =?= instZeroLEOneClass ▶
[Meta.isDefEq] ✅️ NeZero 1 =?= NeZero 1 ▶
[Meta.isDefEq] ✅️ ?m.17989 =?= instNeZeroOne ▶
[Meta.isDefEq] ✅️ NeZero 1 =?= NeZero 1
[Meta.isDefEq] ✅️ ?inst✝ =?= instNeZeroOne ▶
[Meta.Tactic.simp.rewrite] zero_lt_one:1000:
0 < 1
==>
True
[Meta.isDefEq] ✅️ ?p = True =?= (0 < 1) = True ▶
Termination.lean:586:25
[Meta.isDefEq] ✅️ 0 < ?m.18014 =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ 0 < 1 =?= 0 < 1 ▶
Termination.lean:586:48
[Meta.isDefEq] 💥️ AddZeroClass ?m.18112 =?= AddZeroClass ((i : ?m.18132) → ?m.18133 i) ▶
[Meta.isDefEq] 💥️ LE ?m.18112 =?= LE ((i : ?m.18172) → ?m.18173 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.18112 =?= CanonicallyOrderedAdd (WithTop ?m.18183) ▶
[Meta.isDefEq] ✅️ ?m.18109 ≤ ?m.18110 =?= 0 ≤ ?m.18116 ▶
[Meta.isDefEq] 💥️ AddZeroClass ?m.18112 =?= AddZeroClass ((i : ?m.18210) → ?m.18211 i) ▶
[Meta.isDefEq] 💥️ LE ?m.18112 =?= LE ((i : ?m.18249) → ?m.18250 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.18112 =?= CanonicallyOrderedAdd (WithTop ?m.18259) ▶
[Meta.isDefEq] 💥️ AddZeroClass ?m.18268 =?= AddZeroClass ((i : ?m.19413) → ?m.19414 i) ▶
[Meta.isDefEq] 💥️ LE ?m.18268 =?= LE ((i : ?m.19452) → ?m.19453 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.18268 =?= CanonicallyOrderedAdd (WithTop ?m.19462) ▶
[Meta.isDefEq] 💥️ AddZeroClass ?m.18268 =?= AddZeroClass ((i : ?m.20072) → ?m.20073 i) ▶
[Meta.isDefEq] 💥️ LE ?m.18268 =?= LE ((i : ?m.20111) → ?m.20112 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.18268 =?= CanonicallyOrderedAdd (WithTop ?m.20121) ▶
[Meta.isDefEq] ✅️ AddZeroClass ℕ =?= AddZeroClass ?m.20721 ▶
[Meta.isDefEq] ✅️ ?m.20719 =?= AddMonoid.toAddZeroClass ▶
[Meta.isDefEq] ✅️ AddMonoid ℕ =?= AddMonoid ℕ ▶
[Meta.isDefEq] ✅️ ?m.20722 =?= Nat.instAddMonoid ▶
[Meta.isDefEq] ✅️ ?m.20722 =?= Nat.instAddMonoid ▶
[Meta.isDefEq] ✅️ AddZeroClass ℕ =?= AddZeroClass ℕ
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ AddMonoid ℕ =?= AddMonoid ℕ
[Meta.isDefEq] ✅️ ?m.18113 =?= Nat.instAddMonoid.toAddZeroClass ▶
[Meta.isDefEq] ✅️ LE ℕ =?= LE ℕ
[Meta.isDefEq] ✅️ ?m.20732 =?= instLENat ▶
[Meta.isDefEq] ✅️ LE ℕ =?= LE ℕ
[Meta.isDefEq] ✅️ ?m.18114 =?= instLENat ▶
[Meta.isDefEq] ✅️ CanonicallyOrderedAdd ℕ =?= CanonicallyOrderedAdd ℕ ▶
[Meta.isDefEq] ✅️ ?m.20736 =?= Nat.instCanonicallyOrderedAdd ▶
[Meta.isDefEq] ✅️ CanonicallyOrderedAdd ℕ =?= CanonicallyOrderedAdd ℕ ▶
[Meta.isDefEq] ✅️ ?m.18115 =?= Nat.instCanonicallyOrderedAdd ▶
Termination.lean:586:56
[Meta.isDefEq] ✅️ ?m.18112 =?= ?m.18112
Termination.lean:586:47
[Meta.isDefEq] ✅️ 0 ≤ ?m.18116 =?= 0 ≤ ?m.18116 ▶
Termination.lean:586:31
[Meta.isDefEq] 💥️ Add ?m.18268 =?= Add ((i : ?m.18311) → ?m.18312 i) ▶
[Meta.isDefEq] 💥️ LE ?m.18268 =?= LE ((i : ?m.18351) → ?m.18352 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.18268 ?m.18268 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ 1 ≤ mu s + 1 =?= 1 + 0 ≤ 1 + ?m.18116 ▶
[Meta.isDefEq] 💥️ Add ?m.18268 =?= Add ((i : ?m.18743) → ?m.18744 i) ▶
[Meta.isDefEq] 💥️ LE ?m.18268 =?= LE ((i : ?m.18782) → ?m.18783 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.18268 ?m.18268 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] 💥️ Add ?m.18268 =?= Add ((i : ?m.19505) → ?m.19506 i) ▶
[Meta.isDefEq] 💥️ LE ?m.18268 =?= LE ((i : ?m.19544) → ?m.19545 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.18268 ?m.18268 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] 💥️ Add ?m.18268 =?= Add ((i : ?m.20164) → ?m.20165 i) ▶
[Meta.isDefEq] 💥️ LE ?m.18268 =?= LE ((i : ?m.20203) → ?m.20204 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.18268 ?m.18268 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ Add ℕ =?= Add ℕ
[Meta.isDefEq] ✅️ ?m.20749 =?= instAddNat ▶
[Meta.isDefEq] ✅️ Add ℕ =?= Add ℕ
[Meta.isDefEq] ✅️ ?m.18106 =?= instAddNat ▶
[Meta.isDefEq] ✅️ LE ℕ =?= LE ℕ
[Meta.isDefEq] ✅️ instLENat =?= instLENat
[Meta.isDefEq] ✅️ CovariantClass ℕ ℕ (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ?m.20760 ?m.20760 (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.20757 =?= IsOrderedAddMonoid.toAddLeftMono ▶
[Meta.isDefEq] ✅️ IsOrderedAddMonoid ℕ =?= IsOrderedAddMonoid ℕ ▶
[Meta.isDefEq] ✅️ ?m.20763 =?= Nat.instIsOrderedAddMonoid ▶
[Meta.isDefEq] ✅️ ?m.20763 =?= Nat.instIsOrderedAddMonoid ▶
[Meta.isDefEq] ✅️ CovariantClass ℕ ℕ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 =?= AddLeftMono ℕ ▶
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ AddCommMonoid ℕ =?= AddCommMonoid ℕ
[Meta.isDefEq] ✅️ PartialOrder ℕ =?= PartialOrder ℕ
[Meta.isDefEq] ✅️ IsOrderedAddMonoid ℕ =?= IsOrderedAddMonoid ℕ
[Meta.isDefEq] ✅️ ?m.18108 =?= IsOrderedAddMonoid.toAddLeftMono ▶
Termination.lean:586:59
[Meta.isDefEq] ✅️ ?m.18112 =?= ?m.18268 ▶
[Meta.isDefEq] 💥️ OfNat ?m.18268 1 =?= OfNat ℕ+ ?m.18277 ▶
[Meta.isDefEq] ✅️ ?m.18268 =?= ?m.18268
[Meta.isDefEq] 💥️ OfNat ?m.18268 1 =?= OfNat ℕ+ ?m.19473 ▶
[Meta.isDefEq] 💥️ OfNat ?m.18268 1 =?= OfNat ℕ+ ?m.20132 ▶
[Meta.isDefEq] ✅️ ?m.18269 =?= instOfNatNat ?n ▶
Termination.lean:586:30
Application type mismatch: In the application
lt_of_lt_of_le this (add_le_add_left (zero_le ?m.18116) 1)
the argument
add_le_add_left (zero_le ?m.18116) 1
has type
LE.le.{0} (1 + 0) (1 + ?m.18116) : Prop
but is expected to have type
LE.le.{?u.17314 + 1} 1 (mu s + 1) : Prop
Termination.lean:586:10
[Meta.isDefEq] 💥️ Preorder ?m.18011 =?= Preorder ((i : ?m.18045) → ?m.18046 i) ▶
[Meta.isDefEq] ✅️ 0 < mu s + 1 =?= ?m.18013 < ?m.18015 ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17314} =?= Preorder ?m.19387 ▶
[Meta.isDefEq] ✅️ ?m.19385 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17314} =?= PartialOrder Ordinal.{?u.19397} ▶
[Meta.isDefEq] ✅️ ?m.19388 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.19388 =?= partialOrder ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17314} =?= Preorder Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ Type (?u.17314 + 1) =?= Type (?u.17314 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17314} =?= PartialOrder Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ✅️ 0 < mu s + 1 =?= 0 < mu s + 1 ▶
Termination.lean:586:30
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.18116 =?= 1 ≤ mu s + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.18116) ⋯ (1 ≤ mu s + 1) =?= CoeT ?m.19337 ?m.19338 ?m.19337 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.18116 =?= 1 ≤ mu s + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.18116) ⋯ (1 ≤ mu s + 1) =?= CoeT ?m.20043 ?m.20044 ?m.20043 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.18116 =?= 1 ≤ mu s + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.18116) ⋯ (1 ≤ mu s + 1) =?= CoeT ?m.20702 ?m.20703 ?m.20702 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.18116 =?= 1 ≤ mu s + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.18116) ⋯ (1 ≤ mu s + 1) =?= CoeT ?m.21014 ?m.21015 ?m.21014 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.18116 =?= 1 ≤ mu s + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.18116) ⋯ (1 ≤ mu s + 1) =?= CoeT ?m.21184 ?m.21185 ?m.21184 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.18116 =?= 1 ≤ mu s + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.18116) ⋯ (1 ≤ mu s + 1) =?= CoeT ?m.21344 ?m.21345 ?m.21344 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.18116 =?= 1 ≤ mu s + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.18116) ⋯ (1 ≤ mu s + 1) =?= CoeT ?m.21504 ?m.21505 ?m.21504 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.18116 =?= 1 ≤ mu s + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.18116) ⋯ (1 ≤ mu s + 1) =?= CoeT ?m.21664 ?m.21665 ?m.21664 ▶
[Meta.isDefEq] ❌️ @LE.le =?= @LE.le ▶
Termination.lean:588:37
[Meta.isDefEq] ✅️ ?m.22641 < ?m.22642 =?= ω ^ 3 < bigA n ▶
[Meta.isDefEq] ✅️ ω ^ 3 < bigA n =?= ω ^ 3 < bigA n ▶
[Meta.isDefEq] ✅️ ?m.24043 < ?m.24044 =?= ω ^ 3 < bigA n ▶
[Meta.isDefEq] ✅️ ω ^ 3 < bigA n =?= ω ^ 3 < bigA n ▶
Termination.lean:588:2
type mismatch, term
Ordinal.mul_lt_mul_of_pos_left base_lt pos
after simplification has type
Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n : Prop
but is expected to have type
ω ^ 3 _ Order.succ (mu s) < bigA n : Prop
Termination.lean:581:0
[diag] Diagnostics ▼
[reduction] unfolded declarations (max: 427, num: 8): ▶
[reduction] unfolded instances (max: 956, num: 22): ▶
[reduction] unfolded reducible declarations (max: 401, num: 5): ▶
use set*option diagnostics.threshold <num> to control threshold for reporting counters
Termination.lean:582:40
[Meta.isDefEq] ✅️ ω ^ 3 * (mu s + 1) < bigA n =?= ω ^ 3 _ (mu s + 1) < bigA n
Termination.lean:588:2
[Meta.isDefEq] ✅️ ?o + 1 =?= mu s + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu s + 1
==>
Order.succ (mu s)
[Meta.isDefEq] ✅️ ?x > ?y =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?a =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?b =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?a =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?b =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ✅️ ?x > ?y =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?a =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?b =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?a =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?b =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.isDefEq] ✅️ ?x > ?y =?= ω ^ 3 _ Order.succ (mu s) < bigA n ▶
[Meta.Tactic.simp.rewrite] gt*iff_lt:1000:
ω ^ 3 * Order.succ (mu s) < bigA n
==>
ω ^ 3 _ Order.succ (mu s) < bigA n
[Meta.isDefEq] ✅️ ?o + 1 =?= mu s + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu s + 1
==>
Order.succ (mu s)
[Meta.isDefEq] ✅️ ?x > ?y =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a < ?a _ ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a < ?b _ ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a < ?a _ ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a < ?b _ ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ ?a _ ?b < ?a _ ?c =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 < x2 =?= CovariantClass ?m.25025 ?m.25025 (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 < x2 ▶
[Meta.isDefEq] ✅️ ?m.25022 =?= IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono Ordinal.{?u.17314} ▶
[Meta.isDefEq] ✅️ IsLeftCancelMul Ordinal.{?u.17314} =?= IsLeftCancelMul ?m.25036 ▶
[Meta.isDefEq] ✅️ ?m.25027 =?= IsCancelMul.toIsLeftCancelMul ▶
[Meta.isDefEq] ❌️ IsCancelMul Ordinal.{?u.17314} =?= IsCancelMul ?m.25041 ▶
[Meta.isDefEq] ❌️ IsCancelMul Ordinal.{?u.17314} =?= IsCancelMul ?m.25107 ▶
[Meta.isDefEq] ❌️ IsLeftCancelMul Ordinal.{?u.17314} =?= IsLeftCancelMul ?m.25171 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 < x2 =?= CovariantClass ?m.25203 ?m.25203 ?m.25204 fun x1 x2 => x1 < x2 ▶
[Meta.isDefEq] ✅️ ?m.25022 =?= covariant*lt_of_contravariant_le Ordinal.{?u.17314} fun x1 x2 => x1 * x2 ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.25218 ?m.25218 (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.25206 =?= IsLeftCancelMul.mulLeftReflectLE*of_mulLeftReflectLT Ordinal.{?u.17314} ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 * x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.25229 ?m.25229 (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.25441 ?m.25441 (fun x1 x2 => x1 _ x2) ?m.25442 ▶
[Meta.isDefEq] ❌️ ?b _ ?a < ?c _ ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ ?a _ ?b < ?a _ ?c =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.17314} =?= Zero Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ ?inst✝ =?= zero ▶
[Meta.isDefEq] ❌️ ?b _ ?a < ?c _ ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?c _ ?a < ?c _ ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?c < ?b _ ?c =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ ?x > ?y =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a < ?a _ ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a < ?b _ ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a < ?a _ ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a < ?b _ ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?b < ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ ?a _ ?b < ?a _ ?c =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?b _ ?a < ?c _ ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ ?a _ ?b < ?a _ ?c =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.17314} =?= Zero Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ ?inst✝ =?= zero ▶
[Meta.isDefEq] ❌️ ?b _ ?a < ?c _ ?a =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?c _ ?a < ?c _ ?b =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ?a _ ?c < ?b _ ?c =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ (mu s) < bigA n =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ (mu s) < bigA n =?= Order.succ (mu s) _ ω ^ 3 < Order.succ (mu s) _ bigA n ▶
[Meta.isDefEq] ✅️ @LT.lt =?= @LT.lt
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ partialOrder.toLT =?= partialOrder.toLT ▶
[Meta.isDefEq] ❌️ Order.succ (mu s) _ ω ^ 3 =?= ω ^ 3 _ Order.succ (mu s) ▶
[Meta.isDefEq] ❌️ Order.succ (mu s) _ bigA n =?= bigA n ▶
[Meta.isDefEq] ✅️ @HMul.hMul =?= @HMul.hMul
[Meta.isDefEq] ✅️ Ordinal.{u*1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ instHMul =?= instHMul ▶
[Meta.isDefEq] ❌️ Order.succ (mu s) =?= ω ^ 3 ▶
[Meta.isDefEq] ❌️ ω ^ 3 =?= Order.succ (mu s) ▶
Termination.lean:588:14
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.17314} =?= Mul ?m.22702 ▶
[Meta.isDefEq] ✅️ ?m.22695 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.17314} =?= Distrib ?m.22706 ▶
[Meta.isDefEq] ✅️ ?m.22703 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.17314} =?= NonUnitalNonAssocSemiring ?m.22714 ▶
[Meta.isDefEq] ✅️ ?m.22707 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.17314} =?= NonUnitalNonAssocCommSemiring ?m.22719 ▶
[Meta.isDefEq] ✅️ ?m.22715 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.17314} =?= NonUnitalNonAssocCommRing ?m.22724 ▶
[Meta.isDefEq] ✅️ ?m.22720 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.17314} =?= NonUnitalCommRing ?m.22729 ▶
[Meta.isDefEq] ✅️ ?m.22725 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.17314} =?= CommRing ?m.22734 ▶
[Meta.isDefEq] ✅️ ?m.22730 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.17314} =?= NonUnitalNonAssocSemiring ?m.22736 ▶
[Meta.isDefEq] ✅️ ?m.22707 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.17314} =?= NonUnitalNonAssocRing ?m.22741 ▶
[Meta.isDefEq] ✅️ ?m.22737 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.17314} =?= NonUnitalNonAssocRing ?m.22745 ▶
[Meta.isDefEq] ✅️ ?m.22737 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.17314} =?= NonAssocRing ?m.22748 ▶
[Meta.isDefEq] ✅️ ?m.22746 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.17314} =?= Ring ?m.22754 ▶
[Meta.isDefEq] ✅️ ?m.22749 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.17314} =?= DivisionRing ?m.22757 ▶
[Meta.isDefEq] ✅️ ?m.22755 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.17314} =?= Ring ?m.22759 ▶
[Meta.isDefEq] ✅️ ?m.22749 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.17314} =?= NonUnitalNonAssocRing ?m.22761 ▶
[Meta.isDefEq] ✅️ ?m.22737 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.17314} =?= NonUnitalRing ?m.22765 ▶
[Meta.isDefEq] ✅️ ?m.22762 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.17314} =?= NonUnitalRing ?m.22769 ▶
[Meta.isDefEq] ✅️ ?m.22762 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.17314} =?= NonUnitalNonAssocSemiring ?m.22771 ▶
[Meta.isDefEq] ✅️ ?m.22707 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.17314} =?= NonAssocSemiring ?m.22775 ▶
[Meta.isDefEq] ✅️ ?m.22772 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17314} =?= Semiring ?m.22782 ▶
[Meta.isDefEq] ✅️ ?m.22776 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.17314} =?= DivisionSemiring ?m.22787 ▶
[Meta.isDefEq] ✅️ ?m.22783 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.17314} =?= Semifield ?m.22790 ▶
[Meta.isDefEq] ✅️ ?m.22788 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.17314} =?= DivisionSemiring ?m.22792 ▶
[Meta.isDefEq] ✅️ ?m.22783 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17314} =?= Semiring ?m.22794 ▶
[Meta.isDefEq] ✅️ ?m.22776 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.17314} =?= CommSemiring ?m.22798 ▶
[Meta.isDefEq] ✅️ ?m.22795 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.17314} =?= CommSemiring ?m.22800 ▶
[Meta.isDefEq] ✅️ ?m.22795 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17314} =?= Semiring ?m.22802 ▶
[Meta.isDefEq] ✅️ ?m.22776 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.17314} =?= NonAssocSemiring ?m.22804 ▶
[Meta.isDefEq] ✅️ ?m.22772 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.17314} =?= NonUnitalNonAssocSemiring ?m.22806 ▶
[Meta.isDefEq] ✅️ ?m.22707 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.17314} =?= NonUnitalSemiring ?m.22811 ▶
[Meta.isDefEq] ✅️ ?m.22807 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.17314} =?= NonUnitalCommSemiring ?m.22817 ▶
[Meta.isDefEq] ✅️ ?m.22812 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.17314} =?= NonUnitalCommSemiring ?m.22821 ▶
[Meta.isDefEq] ✅️ ?m.22812 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.17314} =?= NonUnitalSemiring ?m.22823 ▶
[Meta.isDefEq] ✅️ ?m.22807 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.17314} =?= NonUnitalSemiring ?m.22825 ▶
[Meta.isDefEq] ✅️ ?m.22807 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.17314} =?= Mul ?m.22827 ▶
[Meta.isDefEq] ✅️ ?m.22695 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.17314} =?= MulZeroClass ?m.22832 ▶
[Meta.isDefEq] ✅️ ?m.22828 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.17314} =?= MulZeroClass ?m.22836 ▶
[Meta.isDefEq] ✅️ ?m.22828 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.17314} =?= MulZeroOneClass ?m.22840 ▶
[Meta.isDefEq] ✅️ ?m.22837 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.17314} =?= MulZeroOneClass ?m.22844 ▶
[Meta.isDefEq] ✅️ ?m.22837 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.17314} =?= MonoidWithZero Ordinal.{?u.22850} ▶
[Meta.isDefEq] ✅️ ?m.22845 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.22845 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.22837 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.22828 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.17314} =?= Mul Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ Type (?u.17314 + 1) =?= Type (?u.17314 + 1)
[Meta.isDefEq] ✅️ Type (?u.17314 + 1) =?= Type (?u.17314 + 1)
[Meta.isDefEq] ✅️ Type (?u.17314 + 1) =?= Type (?u.17314 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.17314} =?= MonoidWithZero Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.17314} =?= MulZeroOneClass Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.17314} =?= MulZeroClass Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ ?m.22637 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.17314} =?= Zero Ordinal.{?u.22860} ▶
[Meta.isDefEq] ✅️ ?m.22854 =?= zero ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.17314} =?= Zero Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ zero =?= zero
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17314} =?= Preorder Ordinal.{?u.17314}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ❌️ PosMulStrictMono Ordinal.{?u.17314} =?= PosMulStrictMono ?m.22865 ▶
[Meta.isDefEq] ❌️ PosMulStrictMono Ordinal.{?u.17314} =?= PosMulStrictMono ?m.22890 ▶
[Meta.isDefEq] ✅️ PosMulStrictMono Ordinal.{?u.17314} =?= PosMulStrictMono ?m.23066 ▶
[Meta.isDefEq] ✅️ ?m.22861 =?= MulLeftStrictMono.toPosMulStrictMono ▶
[Meta.isDefEq] ✅️ MulLeftStrictMono Ordinal.{?u.17314} =?= CovariantClass ?m.23074 ?m.23074 (fun x1 x2 => x1 * x2) fun x1 x2 => x1 < x2 ▶
[Meta.isDefEq] ✅️ ?m.23070 =?= IsLeftCancelMul.mulLeftStrictMono*of_mulLeftMono Ordinal.{?u.17314} ▶
[Meta.isDefEq] ✅️ IsLeftCancelMul Ordinal.{?u.17314} =?= IsLeftCancelMul ?m.23097 ▶
[Meta.isDefEq] ✅️ ?m.23076 =?= IsCancelMul.toIsLeftCancelMul ▶
[Meta.isDefEq] ❌️ IsCancelMul Ordinal.{?u.17314} =?= IsCancelMul ?m.23106 ▶
[Meta.isDefEq] ❌️ IsCancelMul Ordinal.{?u.17314} =?= IsCancelMul ?m.23392 ▶
[Meta.isDefEq] ❌️ IsLeftCancelMul Ordinal.{?u.17314} =?= IsLeftCancelMul ?m.23475 ▶
[Meta.isDefEq] ✅️ MulLeftStrictMono Ordinal.{?u.17314} =?= CovariantClass ?m.23534 ?m.23534 ?m.23535 fun x1 x2 => x1 < x2 ▶
[Meta.isDefEq] ✅️ ?m.23070 =?= covariant_lt_of_contravariant_le Ordinal.{?u.17314} fun x1 x2 => x1 * x2 ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.23556 ?m.23556 (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.23537 =?= IsLeftCancelMul.mulLeftReflectLE*of_mulLeftReflectLT Ordinal.{?u.17314} ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 * x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.23583 ?m.23583 (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17314} Ordinal.{?u.17314} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.23823 ?m.23823 (fun x1 x2 => x1 _ x2) ?m.23824 ▶
Termination.lean:588:45
[Meta.isDefEq] ✅️ 0 < ?m.22640 =?= 0 < mu s + 1 ▶
[Meta.isDefEq] ✅️ 0 < mu s + 1 =?= 0 < mu s + 1 ▶
[Meta.isDefEq] ✅️ 0 < ?m.24045 =?= 0 < mu s + 1 ▶
[Meta.isDefEq] ✅️ 0 < mu s + 1 =?= 0 < mu s + 1 ▶
Termination.lean:590:25
[Meta.isDefEq] ✅️ Sort ?u.17046 =?= Type
[Meta.isDefEq] ✅️ Sort ?u.17048 =?= Type
[Meta.isDefEq] ✅️ Sort ?u.17050 =?= Type
Termination.lean:591:4
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= ?m.17373 ▶
[Meta.isDefEq] ✅️ ?m.17062 =?= ?m.17374 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17111} ?m.17374 ?m.17377 =?= HPow ?m.17382 ?m.17383 ?m.17382 ▶
[Meta.isDefEq] ✅️ ?m.17378 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17111} ?m.17374 =?= Pow Ordinal.{?u.17399} Ordinal.{?u.17399} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17111} ?m.17374 ?m.17493 =?= HPow ?m.17498 ?m.17499 ?m.17498 ▶
[Meta.isDefEq] ✅️ ?m.17494 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17111} ?m.17374 =?= Pow Ordinal.{?u.17512} Ordinal.{?u.17512} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17111} ?m.17374 ?m.17531 =?= HPow ?m.17536 ?m.17537 ?m.17536 ▶
[Meta.isDefEq] ✅️ ?m.17532 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17111} ?m.17374 =?= Pow Ordinal.{?u.17547} Ordinal.{?u.17547} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17111} ?m.17374 ?m.17563 =?= HPow ?m.17568 ?m.17569 ?m.17568 ▶
[Meta.isDefEq] ✅️ ?m.17564 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17111} ?m.17374 =?= Pow Ordinal.{?u.17579} Ordinal.{?u.17579} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17111} ?m.17374 ?m.17595 =?= HPow ?m.17600 ?m.17601 ?m.17600 ▶
[Meta.isDefEq] ✅️ ?m.17596 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17111} ?m.17374 =?= Pow Ordinal.{?u.17611} Ordinal.{?u.17611} ▶
[Meta.isDefEq] ✅️ ?m.17376 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17111} ?β =?= Pow Ordinal.{?u.17636} Ordinal.{?u.17636} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.17111} =?= Monoid Ordinal.{?u.17650} ▶
[Meta.isDefEq] ✅️ ?m.17644 =?= monoid ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.17111} =?= Monoid Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:591:13
[Meta.isDefEq] 💥️ OfNat ?m.17062 2 =?= OfNat ℕ+ ?m.17071 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17062 2 =?= OfNat ℕ+ ?m.17100 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17062 2 =?= OfNat ℕ+ ?m.17118 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17374 2 =?= OfNat ℕ+ ?m.17472 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17374 2 =?= OfNat ℕ+ ?m.17529 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17374 2 =?= OfNat ℕ+ ?m.17561 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17374 2 =?= OfNat ℕ+ ?m.17593 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 2 =?= OfNat ℕ ?m.17656 ▶
[Meta.isDefEq] ✅️ ?m.17653 =?= instOfNatNat 2 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 2 =?= OfNat ℕ 2
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ?m.17064 =?= instOfNatNat 2 ▶
Termination.lean:591:27
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:591:29
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:591:22
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:591:31
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:591:21
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:591:18
[Meta.isDefEq] ✅️ Type ?u.17350 =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Type ?u.17351 =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.17352) =?= Type (?u.17111 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17111} Ordinal.{?u.17111} ?m.17353 =?= HAdd ?m.17356 ?m.17356 ?m.17356 ▶
[Meta.isDefEq] ✅️ ?m.17354 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17111} =?= Add Ordinal.{?u.17370} ▶
[Meta.isDefEq] ✅️ ?m.17357 =?= add ▶
[Meta.isDefEq] ✅️ ?m.17357 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17111} Ordinal.{?u.17111}
Ordinal.{?u.17111} =?= HAdd Ordinal.{?u.17111} Ordinal.{?u.17111} Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17111} =?= Add Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= ?m.17080 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= ?m.17402 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= ?m.17403 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17111} Ordinal.{?u.17111} ?m.17406 =?= HAdd ?m.17409 ?m.17409 ?m.17409 ▶
[Meta.isDefEq] ✅️ ?m.17407 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17111} =?= Add Ordinal.{?u.17420} ▶
[Meta.isDefEq] ✅️ ?m.17410 =?= add ▶
[Meta.isDefEq] ✅️ ?m.17410 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17111} Ordinal.{?u.17111} ?m.17404 =?= HAdd Ordinal.{?u.17111} Ordinal.{?u.17111} Ordinal.{?u.17111} ▶
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17111} =?= Add Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ ?m.17405 =?= instHAdd ▶
Termination.lean:591:36
[Meta.isDefEq] 💥️ OfNat ?m.17080 1 =?= OfNat ℕ+ ?m.17090 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17080 1 =?= OfNat ℕ+ ?m.17109 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17080 1 =?= OfNat ℕ+ ?m.17127 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17111} 1 =?= OfNat ?m.17480 1 ▶
[Meta.isDefEq] ✅️ ?m.17476 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.17111} =?= One Ordinal.{?u.17488} ▶
[Meta.isDefEq] ✅️ ?m.17481 =?= one ▶
[Meta.isDefEq] ✅️ ?m.17481 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17111} 1 =?= OfNat Ordinal.{?u.17111} 1
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.17111} =?= One Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ ?m.17082 =?= One.toOfNat1 ▶
Termination.lean:591:4
[Meta.isDefEq] ✅️ Type ?u.17165 =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Type ?u.17166 =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.17167) =?= Type (?u.17111 + 1) ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.17111} Ordinal.{?u.17111} ?m.17168 =?= HMul ?m.17171 ?m.17171 ?m.17171 ▶
[Meta.isDefEq] ✅️ ?m.17169 =?= instHMul ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.17111} =?= Mul ?m.17185 ▶
[Meta.isDefEq] ✅️ ?m.17172 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.17111} =?= Distrib ?m.17190 ▶
[Meta.isDefEq] ✅️ ?m.17186 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.17111} =?= NonUnitalNonAssocSemiring ?m.17198 ▶
[Meta.isDefEq] ✅️ ?m.17191 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.17111} =?= NonUnitalNonAssocCommSemiring ?m.17203 ▶
[Meta.isDefEq] ✅️ ?m.17199 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.17111} =?= NonUnitalNonAssocCommRing ?m.17208 ▶
[Meta.isDefEq] ✅️ ?m.17204 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.17111} =?= NonUnitalCommRing ?m.17213 ▶
[Meta.isDefEq] ✅️ ?m.17209 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.17111} =?= CommRing ?m.17218 ▶
[Meta.isDefEq] ✅️ ?m.17214 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.17111} =?= NonUnitalNonAssocSemiring ?m.17222 ▶
[Meta.isDefEq] ✅️ ?m.17191 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.17111} =?= NonUnitalNonAssocRing ?m.17227 ▶
[Meta.isDefEq] ✅️ ?m.17223 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.17111} =?= NonUnitalNonAssocRing ?m.17231 ▶
[Meta.isDefEq] ✅️ ?m.17223 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.17111} =?= NonAssocRing ?m.17234 ▶
[Meta.isDefEq] ✅️ ?m.17232 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.17111} =?= Ring ?m.17240 ▶
[Meta.isDefEq] ✅️ ?m.17235 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.17111} =?= DivisionRing ?m.17245 ▶
[Meta.isDefEq] ✅️ ?m.17241 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.17111} =?= Ring ?m.17249 ▶
[Meta.isDefEq] ✅️ ?m.17235 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.17111} =?= NonUnitalNonAssocRing ?m.17251 ▶
[Meta.isDefEq] ✅️ ?m.17223 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.17111} =?= NonUnitalRing ?m.17255 ▶
[Meta.isDefEq] ✅️ ?m.17252 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.17111} =?= NonUnitalRing ?m.17259 ▶
[Meta.isDefEq] ✅️ ?m.17252 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.17111} =?= NonUnitalNonAssocSemiring ?m.17261 ▶
[Meta.isDefEq] ✅️ ?m.17191 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.17111} =?= NonAssocSemiring ?m.17265 ▶
[Meta.isDefEq] ✅️ ?m.17262 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17111} =?= Semiring ?m.17272 ▶
[Meta.isDefEq] ✅️ ?m.17266 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.17111} =?= DivisionSemiring ?m.17278 ▶
[Meta.isDefEq] ✅️ ?m.17273 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.17111} =?= Semifield ?m.17283 ▶
[Meta.isDefEq] ✅️ ?m.17279 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.17111} =?= DivisionSemiring ?m.17287 ▶
[Meta.isDefEq] ✅️ ?m.17273 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17111} =?= Semiring ?m.17289 ▶
[Meta.isDefEq] ✅️ ?m.17266 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.17111} =?= CommSemiring ?m.17293 ▶
[Meta.isDefEq] ✅️ ?m.17290 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.17111} =?= CommSemiring ?m.17297 ▶
[Meta.isDefEq] ✅️ ?m.17290 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.17111} =?= Semiring ?m.17299 ▶
[Meta.isDefEq] ✅️ ?m.17266 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.17111} =?= NonAssocSemiring ?m.17301 ▶
[Meta.isDefEq] ✅️ ?m.17262 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.17111} =?= NonUnitalNonAssocSemiring ?m.17303 ▶
[Meta.isDefEq] ✅️ ?m.17191 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.17111} =?= NonUnitalSemiring ?m.17308 ▶
[Meta.isDefEq] ✅️ ?m.17304 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.17111} =?= NonUnitalCommSemiring ?m.17314 ▶
[Meta.isDefEq] ✅️ ?m.17309 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.17111} =?= NonUnitalCommSemiring ?m.17318 ▶
[Meta.isDefEq] ✅️ ?m.17309 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.17111} =?= NonUnitalSemiring ?m.17320 ▶
[Meta.isDefEq] ✅️ ?m.17304 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.17111} =?= NonUnitalSemiring ?m.17322 ▶
[Meta.isDefEq] ✅️ ?m.17304 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.17111} =?= Mul ?m.17324 ▶
[Meta.isDefEq] ✅️ ?m.17172 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.17111} =?= MulZeroClass ?m.17329 ▶
[Meta.isDefEq] ✅️ ?m.17325 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.17111} =?= MulZeroClass ?m.17333 ▶
[Meta.isDefEq] ✅️ ?m.17325 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.17111} =?= MulZeroOneClass ?m.17337 ▶
[Meta.isDefEq] ✅️ ?m.17334 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.17111} =?= MulZeroOneClass ?m.17341 ▶
[Meta.isDefEq] ✅️ ?m.17334 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.17111} =?= MonoidWithZero Ordinal.{?u.17347} ▶
[Meta.isDefEq] ✅️ ?m.17342 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.17342 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.17334 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.17325 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ ?m.17172 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.17111} Ordinal.{?u.17111}
Ordinal.{?u.17111} =?= HMul Ordinal.{?u.17111} Ordinal.{?u.17111} Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.17111} =?= MonoidWithZero Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.17111} =?= MulZeroOneClass Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.17111} =?= MulZeroClass Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.17111} =?= Mul Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ ?m.17375 =?= ?m.17427 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= ?m.17428 ▶
[Meta.isDefEq] 💥️ HMul ?m.17427 Ordinal.{?u.17111} ?m.17431 =?= HMul ?m.17436 ?m.17436 ?m.17436 ▶
[Meta.isDefEq] 💥️ HMul ?m.17427 Ordinal.{?u.17111} ?m.17513 =?= HMul ?m.17518 ?m.17518 ?m.17518 ▶
[Meta.isDefEq] 💥️ HMul ?m.17427 Ordinal.{?u.17111} ?m.17548 =?= HMul ?m.17553 ?m.17553 ?m.17553 ▶
[Meta.isDefEq] 💥️ HMul ?m.17427 Ordinal.{?u.17111} ?m.17580 =?= HMul ?m.17585 ?m.17585 ?m.17585 ▶
[Meta.isDefEq] 💥️ HMul ?m.17427 Ordinal.{?u.17111} ?m.17612 =?= HMul ?m.17617 ?m.17617 ?m.17617 ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.17111} Ordinal.{?u.17111}
Ordinal.{?u.17111} =?= HMul Ordinal.{?u.17111} Ordinal.{?u.17111} Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ ?m.17430 =?= instHMul ▶
Termination.lean:591:4
[Meta.isDefEq] 💥️ Ordinal.{?u.17060} =?= Ordinal.{?u.17078}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17078} x Ordinal.{?u.17060} =?= CoeT ?m.17136 ?m.17137 ?m.17136 ▶
[Meta.isDefEq] ✅️ ?m.17130 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17078} x Ordinal.{?u.17060} =?= CoeT Ordinal.{?u.17078} x Ordinal.{?u.17078} ▶
[Meta.isDefEq] ✅️ Type (?u.17078 + 1) =?= Type (?u.17078 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17078} =?= Ordinal.{?u.17078}
[Meta.isDefEq] ✅️ Ordinal.{?u.17078} =?= Ordinal.{?u.17078}
[Meta.isDefEq] 💥️ Ordinal.{?u.17078} =?= Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17111} x Ordinal.{?u.17078} =?= CoeT ?m.17154 ?m.17155 ?m.17154 ▶
[Meta.isDefEq] ✅️ ?m.17148 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17111} x Ordinal.{?u.17078} =?= CoeT Ordinal.{?u.17111} x Ordinal.{?u.17111} ▶
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ ?m.17429 =?= ?m.17441 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17111} =?= ?m.17441 ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17111} =?= LT ?m.17446 ▶
[Meta.isDefEq] ✅️ ?m.17443 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17111} =?= Preorder ?m.17450 ▶
[Meta.isDefEq] ✅️ ?m.17447 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17111} =?= PartialOrder Ordinal.{?u.17462} ▶
[Meta.isDefEq] ✅️ ?m.17451 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17451 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17447 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17111} =?= LT Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ Type (?u.17111 + 1) =?= Type (?u.17111 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17111} =?= PartialOrder Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17111} =?= Preorder Ordinal.{?u.17111}
[Meta.isDefEq] ✅️ ?m.17442 =?= partialOrder.toLT ▶
Termination.lean:591:46
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:593:2
[Meta.isDefEq] ✅️ ω ^ 2 < ω ^ 3 =?= ω ^ 2 < ω ^ 3
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 \* (mu (b.recΔ s n) + 1) < bigA n ▶
Termination.lean:593:18
[Meta.isDefEq] ✅️ Ordinal.{?u.17704} =?= Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ Ordinal.{?u.17704} =?= ?m.17753 ▶
[Meta.isDefEq] ✅️ ?m.17680 =?= ?m.17754 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17754 ?m.17757 =?= HPow ?m.17762 ?m.17763 ?m.17762 ▶
[Meta.isDefEq] ✅️ ?m.17758 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17754 =?= Pow Ordinal.{?u.17779} Ordinal.{?u.17779} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17754 ?m.17857 =?= HPow ?m.17862 ?m.17863 ?m.17862 ▶
[Meta.isDefEq] ✅️ ?m.17858 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17754 =?= Pow Ordinal.{?u.17876} Ordinal.{?u.17876} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17754 ?m.17936 =?= HPow ?m.17941 ?m.17942 ?m.17941 ▶
[Meta.isDefEq] ✅️ ?m.17937 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17754 =?= Pow Ordinal.{?u.17952} Ordinal.{?u.17952} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17754 ?m.18009 =?= HPow ?m.18014 ?m.18015 ?m.18014 ▶
[Meta.isDefEq] ✅️ ?m.18010 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17754 =?= Pow Ordinal.{?u.18025} Ordinal.{?u.18025} ▶
[Meta.isDefEq] ✅️ ?m.17756 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?β =?= Pow Ordinal.{?u.18083} Ordinal.{?u.18083} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.17704} =?= Monoid Ordinal.{?u.18097} ▶
[Meta.isDefEq] ✅️ ?m.18091 =?= monoid ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.17704} =?= Monoid Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:593:27
[Meta.isDefEq] 💥️ OfNat ?m.17680 2 =?= OfNat ℕ+ ?m.17689 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17680 2 =?= OfNat ℕ+ ?m.17699 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17680 2 =?= OfNat ℕ+ ?m.17725 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17754 2 =?= OfNat ℕ+ ?m.17843 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17754 2 =?= OfNat ℕ+ ?m.17926 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17754 2 =?= OfNat ℕ+ ?m.17999 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 2 =?= OfNat ℕ ?m.18103 ▶
[Meta.isDefEq] ✅️ ?m.18100 =?= instOfNatNat 2 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 2 =?= OfNat ℕ 2
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ?m.17682 =?= instOfNatNat 2 ▶
Termination.lean:593:18
[Meta.isDefEq] 💥️ Ordinal.{?u.17678} =?= Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17704} x Ordinal.{?u.17678} =?= CoeT ?m.17742 ?m.17743 ?m.17742 ▶
[Meta.isDefEq] ✅️ ?m.17736 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17704} x Ordinal.{?u.17678} =?= CoeT Ordinal.{?u.17704} x Ordinal.{?u.17704} ▶
[Meta.isDefEq] ✅️ Type (?u.17704 + 1) =?= Type (?u.17704 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17704} =?= Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ Ordinal.{?u.17704} =?= Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ ?m.17755 =?= ?m.17811 ▶
[Meta.isDefEq] ✅️ ?m.17784 =?= ?m.17811 ▶
[Meta.isDefEq] 💥️ LT ?m.17811 =?= LT (Option ?m.17834) ▶
[Meta.isDefEq] 💥️ LT ?m.17811 =?= LT (Option ?m.17918) ▶
[Meta.isDefEq] 💥️ LT ?m.17811 =?= LT (Option ?m.17991) ▶
[Meta.isDefEq] 💥️ LT ?m.17811 =?= LT (Option ?m.18064) ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17704} =?= LT ?m.18139 ▶
[Meta.isDefEq] ✅️ ?m.18136 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17704} =?= Preorder ?m.18143 ▶
[Meta.isDefEq] ✅️ ?m.18140 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17704} =?= PartialOrder Ordinal.{?u.18155} ▶
[Meta.isDefEq] ✅️ ?m.18144 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18144 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18140 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17704} =?= LT Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ Type (?u.17704 + 1) =?= Type (?u.17704 + 1)
[Meta.isDefEq] ✅️ Type (?u.17704 + 1) =?= Type (?u.17704 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17704} =?= PartialOrder Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17704} =?= Preorder Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ ?m.17812 =?= partialOrder.toLT ▶
Termination.lean:593:31
[Meta.isDefEq] ✅️ Ordinal.{?u.17704} =?= Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ Ordinal.{?u.17704} =?= ?m.17782 ▶
[Meta.isDefEq] ✅️ ?m.17706 =?= ?m.17783 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17783 ?m.17786 =?= HPow ?m.17791 ?m.17792 ?m.17791 ▶
[Meta.isDefEq] ✅️ ?m.17787 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17783 =?= Pow Ordinal.{?u.17808} Ordinal.{?u.17808} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17783 ?m.17877 =?= HPow ?m.17882 ?m.17883 ?m.17882 ▶
[Meta.isDefEq] ✅️ ?m.17878 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17783 =?= Pow Ordinal.{?u.17896} Ordinal.{?u.17896} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17783 ?m.17953 =?= HPow ?m.17958 ?m.17959 ?m.17958 ▶
[Meta.isDefEq] ✅️ ?m.17954 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17783 =?= Pow Ordinal.{?u.17969} Ordinal.{?u.17969} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17783 ?m.18026 =?= HPow ?m.18031 ?m.18032 ?m.18031 ▶
[Meta.isDefEq] ✅️ ?m.18027 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17783 =?= Pow Ordinal.{?u.18042} Ordinal.{?u.18042} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17783 ?m.18116 =?= HPow ?m.18121 ?m.18122 ?m.18121 ▶
[Meta.isDefEq] ✅️ ?m.18117 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17783 =?= Pow Ordinal.{?u.18135} Ordinal.{?u.18135} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17783 ?m.18167 =?= HPow ?m.18172 ?m.18173 ?m.18172 ▶
[Meta.isDefEq] ✅️ ?m.18168 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17783 =?= Pow Ordinal.{?u.18183} Ordinal.{?u.18183} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.17704} ?m.17783 ?m.18192 =?= HPow ?m.18197 ?m.18198 ?m.18197 ▶
[Meta.isDefEq] ✅️ ?m.18193 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?m.17783 =?= Pow Ordinal.{?u.18208} Ordinal.{?u.18208} ▶
[Meta.isDefEq] ✅️ ?m.17785 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.17704} ?β =?= Pow Ordinal.{?u.18226} Ordinal.{?u.18226} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.17704} =?= Monoid Ordinal.{?u.17704}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:593:40
[Meta.isDefEq] 💥️ OfNat ?m.17706 3 =?= OfNat ℕ+ ?m.17715 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17706 3 =?= OfNat ℕ+ ?m.17733 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17783 3 =?= OfNat ℕ+ ?m.17853 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17783 3 =?= OfNat ℕ+ ?m.17934 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17783 3 =?= OfNat ℕ+ ?m.18007 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17783 3 =?= OfNat ℕ+ ?m.18114 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17783 3 =?= OfNat ℕ+ ?m.18165 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17783 3 =?= OfNat ℕ+ ?m.18190 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ ?m.18237 ▶
[Meta.isDefEq] ✅️ ?m.18234 =?= instOfNatNat 3 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ 3
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ?m.17708 =?= instOfNatNat 3 ▶
Termination.lean:594:4
[Meta.isDefEq] ✅️ 2 < 3 =?= 2 < 3
[Meta.isDefEq] ✅️ ω ^ 2 < ω ^ 3 =?= ω ^ 2 < ω ^ 3
[Meta.isDefEq] ✅️ ω ^ 2 < ω ^ 3 =?= ω ^ 2 < ω ^ 3 ▶
Termination.lean:594:12
[Meta.isDefEq] ✅️ Ordinal.{?u.18246} =?= ?m.18248 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18246} 2 =?= OfNat ?m.18253 ?m.18254 ▶
[Meta.isDefEq] ✅️ ?m.18250 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.18246} =?= NatCast ?m.18260 ▶
[Meta.isDefEq] ✅️ ?m.18255 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.18246} =?= AddMonoidWithOne Ordinal.{?u.18266} ▶
[Meta.isDefEq] ✅️ ?m.18261 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.18261 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.18255 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 2 =?= (?m.18269 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.18256 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.18256 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18246} 2 =?= OfNat Ordinal.{?u.18246} 2
[Meta.isDefEq] ✅️ Type (?u.18246 + 1) =?= Type (?u.18246 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.18246 + 1) =?= Type (?u.18246 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.18246} =?= AddMonoidWithOne Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.18246} =?= NatCast Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 0 =?= OfNat ℕ 0
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 2 =?= (0 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.18249 =?= instOfNatAtLeastTwo ▶
Termination.lean:594:16
[Meta.isDefEq] ✅️ Sort ?u.18245 =?= Type (?u.18246 + 1)
Termination.lean:594:11
[Meta.isDefEq] ✅️ Ordinal.{?u.18246} =?= Ordinal.{?u.18246}
Termination.lean:594:11
[Meta.isDefEq] ✅️ Ordinal.{?u.18246} =?= Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ Ordinal.{?u.18246} =?= ?m.18276 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.18246} =?= ?m.18297 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.18246} =?= Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ LT Ordinal.{?u.18246} =?= LT ?m.18302 ▶
[Meta.isDefEq] ✅️ ?m.18299 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18246} =?= Preorder ?m.18306 ▶
[Meta.isDefEq] ✅️ ?m.18303 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.18246} =?= PartialOrder Ordinal.{?u.18318} ▶
[Meta.isDefEq] ✅️ ?m.18307 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18307 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18303 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.18246} =?= LT Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ Type (?u.18246 + 1) =?= Type (?u.18246 + 1)
[Meta.isDefEq] ✅️ Type (?u.18246 + 1) =?= Type (?u.18246 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.18246} =?= PartialOrder Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18246} =?= Preorder Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ ?m.18298 =?= partialOrder.toLT ▶
Termination.lean:594:27
[Meta.isDefEq] 💥️ OfNat ?m.18276 3 =?= OfNat ℕ+ ?m.18285 ▶
[Meta.isDefEq] 💥️ OfNat ?m.18276 3 =?= OfNat ℕ+ ?m.18295 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18246} 3 =?= OfNat ?m.18325 ?m.18326 ▶
[Meta.isDefEq] ✅️ ?m.18322 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.18246} =?= NatCast ?m.18330 ▶
[Meta.isDefEq] ✅️ ?m.18327 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.18246} =?= AddMonoidWithOne Ordinal.{?u.18334} ▶
[Meta.isDefEq] ✅️ ?m.18331 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.18331 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.18327 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 3 =?= (?m.18335 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.18328 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.18328 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18246} 3 =?= OfNat Ordinal.{?u.18246} 3
[Meta.isDefEq] ✅️ Type (?u.18246 + 1) =?= Type (?u.18246 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.18246 + 1) =?= Type (?u.18246 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.18246} =?= AddMonoidWithOne Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.18246} =?= NatCast Ordinal.{?u.18246}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 1 =?= OfNat ℕ 1
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 3 =?= (1 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.18278 =?= instOfNatAtLeastTwo ▶
Termination.lean:594:35
simp made no progress
Termination.lean:594:35
[Meta.isDefEq] ✅️ ?x > ?y =?= 2 < 3 ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= 2 < 3 ▶
Termination.lean:595:35
[Meta.isDefEq] ✅️ ?m.18592 < ?m.18593 =?= 0 < ω ▶
[Meta.isDefEq] ✅️ 0 < ω =?= 0 < ω ▶
Termination.lean:595:16
Function expected at
opow_lt_opow_right omega0_pos
but this term has type
ω ^ 0 < ω ^ ω

Note: Expected a function because this term is being applied to the argument
this
Termination.lean:595:4
[Meta.isDefEq] ✅️ ?x > ?y =?= ω ^ 2 < ω ^ 3 ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= ω ^ 2 < ω ^ 3 ▶
[Meta.isDefEq] ✅️ ?x > ?y =?= ω ^ 2 < ω ^ 3 ▶
[Meta.Tactic.simp.rewrite] gt*iff_lt:1000:
ω ^ 2 < ω ^ 3
==>
ω ^ 2 < ω ^ 3
[Meta.isDefEq] ❌️ fun as => Array.filterMap some as =?= ?m.18650 ▶
[Meta.isDefEq] ✅️ ω ^ 2 < ω ^ 3 =?= ?m.18650 ▶
[Meta.isDefEq] ✅️ ω ^ 2 < ω ^ 3 =?= ω ^ 2 < ω ^ 3
Termination.lean:595:16
[Meta.isDefEq] ✅️ CoeFun (ω ^ 0 < ω ^ ω) ?m.18615 =?= CoeFun ?m.18620 fun x => (a : ?m.18621) → ?m.18622 a ▶
[Meta.isDefEq] ✅️ ?m.18616 =?= DFunLike.hasCoeToFun ▶
[Meta.isDefEq] ✅️ DFunLike (ω ^ 0 < ω ^ ω) ?m.18621 ?m.18622 =?= DFunLike ?m.18638 ?m.18639 fun x => ?m.18640 ▶
[Meta.isDefEq] ✅️ ?m.18623 =?= EquivLike.toFunLike ▶
Termination.lean:596:2
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= 0 < mu (b.recΔ s n) + 1
[Meta.isDefEq] ✅️ ω ^ 2 * (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n
Termination.lean:596:14
[Meta.isDefEq] ✅️ Ordinal.{?u.18768} =?= ?m.18770 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18768} 0 =?= OfNat ?m.18776 0 ▶
[Meta.isDefEq] ✅️ ?m.18772 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.18768} =?= Zero Ordinal.{?u.18785} ▶
[Meta.isDefEq] ✅️ ?m.18777 =?= zero ▶
[Meta.isDefEq] ✅️ ?m.18777 =?= zero ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18768} 0 =?= OfNat Ordinal.{?u.18768} 0
[Meta.isDefEq] ✅️ Type (?u.18768 + 1) =?= Type (?u.18768 + 1)
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.18768} =?= Zero Ordinal.{?u.18768}
[Meta.isDefEq] ✅️ ?m.18771 =?= Zero.toOfNat0 ▶
Termination.lean:596:18
[Meta.isDefEq] ✅️ Sort ?u.18767 =?= Type (?u.18768 + 1)
Termination.lean:596:13
[Meta.isDefEq] ✅️ Ordinal.{?u.18768} =?= Ordinal.{?u.18768}
Termination.lean:596:38
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:596:40
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:596:33
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:596:42
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:596:32
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:596:13
[Meta.isDefEq] 💥️ Ordinal.{?u.18768} =?= Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.18793} x Ordinal.{?u.18768} =?= CoeT ?m.18825 ?m.18826 ?m.18825 ▶
[Meta.isDefEq] ✅️ ?m.18819 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.18793} x Ordinal.{?u.18768} =?= CoeT Ordinal.{?u.18793} x Ordinal.{?u.18793} ▶
[Meta.isDefEq] ✅️ Type (?u.18793 + 1) =?= Type (?u.18793 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= ?m.18884 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ LT Ordinal.{?u.18793} =?= LT ?m.18889 ▶
[Meta.isDefEq] ✅️ ?m.18886 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18793} =?= Preorder ?m.18893 ▶
[Meta.isDefEq] ✅️ ?m.18890 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.18793} =?= PartialOrder Ordinal.{?u.18905} ▶
[Meta.isDefEq] ✅️ ?m.18894 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18894 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18890 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.18793} =?= LT Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ Type (?u.18793 + 1) =?= Type (?u.18793 + 1)
[Meta.isDefEq] ✅️ Type (?u.18793 + 1) =?= Type (?u.18793 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.18793} =?= PartialOrder Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18793} =?= Preorder Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ ?m.18885 =?= partialOrder.toLT ▶
Termination.lean:596:29
[Meta.isDefEq] ✅️ Type ?u.18836 =?= Type (?u.18793 + 1)
[Meta.isDefEq] ✅️ Type ?u.18837 =?= Type (?u.18793 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.18838) =?= Type (?u.18793 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.18793} Ordinal.{?u.18793} ?m.18839 =?= HAdd ?m.18842 ?m.18842 ?m.18842 ▶
[Meta.isDefEq] ✅️ ?m.18840 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.18793} =?= Add Ordinal.{?u.18856} ▶
[Meta.isDefEq] ✅️ ?m.18843 =?= add ▶
[Meta.isDefEq] ✅️ ?m.18843 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.18793} Ordinal.{?u.18793}
Ordinal.{?u.18793} =?= HAdd Ordinal.{?u.18793} Ordinal.{?u.18793} Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ Type (?u.18793 + 1) =?= Type (?u.18793 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.18793} =?= Add Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= ?m.18795 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= ?m.18859 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.18793} =?= ?m.18860 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.18793} Ordinal.{?u.18793} ?m.18863 =?= HAdd ?m.18866 ?m.18866 ?m.18866 ▶
[Meta.isDefEq] ✅️ ?m.18864 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.18793} =?= Add Ordinal.{?u.18877} ▶
[Meta.isDefEq] ✅️ ?m.18867 =?= add ▶
[Meta.isDefEq] ✅️ ?m.18867 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.18793} Ordinal.{?u.18793} ?m.18861 =?= HAdd Ordinal.{?u.18793} Ordinal.{?u.18793} Ordinal.{?u.18793} ▶
[Meta.isDefEq] ✅️ Type (?u.18793 + 1) =?= Type (?u.18793 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.18793} =?= Add Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ ?m.18862 =?= instHAdd ▶
Termination.lean:596:47
[Meta.isDefEq] 💥️ OfNat ?m.18795 1 =?= OfNat ℕ+ ?m.18805 ▶
[Meta.isDefEq] 💥️ OfNat ?m.18795 1 =?= OfNat ℕ+ ?m.18816 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18793} 1 =?= OfNat ?m.18913 1 ▶
[Meta.isDefEq] ✅️ ?m.18909 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.18793} =?= One Ordinal.{?u.18921} ▶
[Meta.isDefEq] ✅️ ?m.18914 =?= one ▶
[Meta.isDefEq] ✅️ ?m.18914 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18793} 1 =?= OfNat Ordinal.{?u.18793} 1
[Meta.isDefEq] ✅️ Type (?u.18793 + 1) =?= Type (?u.18793 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.18793} =?= One Ordinal.{?u.18793}
[Meta.isDefEq] ✅️ ?m.18797 =?= One.toOfNat1 ▶
Termination.lean:597:4
[Meta.isDefEq] ✅️ 0 < 1 =?= 0 < 1
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= 0 < mu (b.recΔ s n) + 1
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= 0 < mu (b.recΔ s n) + 1 ▶
Termination.lean:597:12
[Meta.isDefEq] ✅️ Ordinal.{?u.18934} =?= ?m.18936 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18934} 0 =?= OfNat ?m.18942 0 ▶
[Meta.isDefEq] ✅️ ?m.18938 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.18934} =?= Zero Ordinal.{?u.18951} ▶
[Meta.isDefEq] ✅️ ?m.18943 =?= zero ▶
[Meta.isDefEq] ✅️ ?m.18943 =?= zero ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18934} 0 =?= OfNat Ordinal.{?u.18934} 0
[Meta.isDefEq] ✅️ Type (?u.18934 + 1) =?= Type (?u.18934 + 1)
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.18934} =?= Zero Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ ?m.18937 =?= Zero.toOfNat0 ▶
Termination.lean:597:16
[Meta.isDefEq] ✅️ Sort ?u.18933 =?= Type (?u.18934 + 1)
Termination.lean:597:11
[Meta.isDefEq] ✅️ Ordinal.{?u.18934} =?= Ordinal.{?u.18934}
Termination.lean:597:11
[Meta.isDefEq] ✅️ Ordinal.{?u.18934} =?= Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ Ordinal.{?u.18934} =?= ?m.18957 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.18934} =?= ?m.18980 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.18934} =?= Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ LT Ordinal.{?u.18934} =?= LT ?m.18985 ▶
[Meta.isDefEq] ✅️ ?m.18982 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18934} =?= Preorder ?m.18989 ▶
[Meta.isDefEq] ✅️ ?m.18986 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.18934} =?= PartialOrder Ordinal.{?u.19001} ▶
[Meta.isDefEq] ✅️ ?m.18990 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18990 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18986 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.18934} =?= LT Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ Type (?u.18934 + 1) =?= Type (?u.18934 + 1)
[Meta.isDefEq] ✅️ Type (?u.18934 + 1) =?= Type (?u.18934 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.18934} =?= PartialOrder Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18934} =?= Preorder Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ ?m.18981 =?= partialOrder.toLT ▶
Termination.lean:597:27
[Meta.isDefEq] 💥️ OfNat ?m.18957 1 =?= OfNat ℕ+ ?m.18967 ▶
[Meta.isDefEq] 💥️ OfNat ?m.18957 1 =?= OfNat ℕ+ ?m.18978 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18934} 1 =?= OfNat ?m.19009 1 ▶
[Meta.isDefEq] ✅️ ?m.19005 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.18934} =?= One Ordinal.{?u.19015} ▶
[Meta.isDefEq] ✅️ ?m.19010 =?= one ▶
[Meta.isDefEq] ✅️ ?m.19010 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.18934} 1 =?= OfNat Ordinal.{?u.18934} 1
[Meta.isDefEq] ✅️ Type (?u.18934 + 1) =?= Type (?u.18934 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.18934} =?= One Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ ?m.18959 =?= One.toOfNat1 ▶
Termination.lean:597:35
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.18934} =?= AddMonoidWithOne Ordinal.{?u.19026} ▶
[Meta.isDefEq] ✅️ ?m.19023 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.18934} =?= AddMonoidWithOne Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ OfNat.ofNat ?m.19028 =?= 0 ▶
[Meta.isDefEq] ✅️ 0 =?= 0 ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.18934} =?= AddMonoidWithOne Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ OfNat.ofNat ?m.19040 =?= 1 ▶
[Meta.isDefEq] ✅️ 1 =?= 1 ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.18934} =?= LT Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ LT.lt =?= LT.lt
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.18934} =?= Semiring ?m.19050 ▶
[Meta.isDefEq] ✅️ ?m.19046 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.18934} =?= DivisionSemiring ?m.19055 ▶
[Meta.isDefEq] ✅️ ?m.19051 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.18934} =?= Semifield ?m.19060 ▶
[Meta.isDefEq] ✅️ ?m.19056 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.18934} =?= DivisionSemiring ?m.19064 ▶
[Meta.isDefEq] ✅️ ?m.19051 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.18934} =?= DivisionRing ?m.19067 ▶
[Meta.isDefEq] ✅️ ?m.19065 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.18934} =?= Semiring ?m.19071 ▶
[Meta.isDefEq] ✅️ ?m.19046 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.18934} =?= CommSemiring ?m.19075 ▶
[Meta.isDefEq] ✅️ ?m.19072 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.18934} =?= CommSemiring ?m.19079 ▶
[Meta.isDefEq] ✅️ ?m.19072 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.18934} =?= CommRing ?m.19082 ▶
[Meta.isDefEq] ✅️ ?m.19080 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.18934} =?= Semiring ?m.19086 ▶
[Meta.isDefEq] ✅️ ?m.19046 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.18934} =?= Ring ?m.19090 ▶
[Meta.isDefEq] ✅️ ?m.19087 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.18934} =?= Ring ?m.19094 ▶
[Meta.isDefEq] ✅️ ?m.19087 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ ?x > ?y =?= 0 < 1 ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ OfNat.ofNat ?n < 1 =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.18934} Ordinal.{?u.18934} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass Ordinal.{?u.19264} Ordinal.{?u.19264} (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.19261 =?= instAddLeftMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.18934} Ordinal.{?u.18934} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddLeftMono Ordinal.{?u.18934} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddLeftMono ▶
[Meta.isDefEq] ✅️ ZeroLEOneClass Ordinal.{?u.18934} =?= ZeroLEOneClass Ordinal.{?u.19398} ▶
[Meta.isDefEq] ✅️ ?m.19392 =?= instZeroLEOneClass ▶
[Meta.isDefEq] ✅️ ZeroLEOneClass Ordinal.{?u.18934} =?= ZeroLEOneClass Ordinal.{?u.18934} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instZeroLEOneClass ▶
[Meta.isDefEq] ✅️ CharZero Ordinal.{?u.18934} =?= CharZero Ordinal.{?u.19425} ▶
[Meta.isDefEq] ✅️ ?m.19423 =?= instCharZero ▶
[Meta.isDefEq] ✅️ CharZero Ordinal.{?u.18934} =?= CharZero Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ ?inst✝ =?= instCharZero ▶
[Meta.isDefEq] ❌️ Nat.AtLeastTwo 0 =?= (?m.19431 + 2).AtLeastTwo ▶
[Meta.isDefEq] ❌️ 0 < OfNat.ofNat ?n =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ 0 < 1 =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ ZeroLEOneClass Ordinal.{?u.18934} =?= ZeroLEOneClass Ordinal.{?u.19607} ▶
[Meta.isDefEq] ✅️ ?m.19601 =?= instZeroLEOneClass ▶
[Meta.isDefEq] ✅️ ZeroLEOneClass Ordinal.{?u.18934} =?= ZeroLEOneClass Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ ?inst✝ =?= instZeroLEOneClass ▶
[Meta.isDefEq] ✅️ NeZero 1 =?= NeZero 1 ▶
[Meta.isDefEq] ✅️ ?m.19608 =?= instNeZeroOne ▶
[Meta.isDefEq] ✅️ NeZero 1 =?= NeZero 1
[Meta.isDefEq] ✅️ ?inst✝ =?= instNeZeroOne ▶
[Meta.Tactic.simp.rewrite] zero_lt_one:1000:
0 < 1
==>
True
[Meta.isDefEq] ✅️ ?p = True =?= (0 < 1) = True ▶
Termination.lean:598:25
[Meta.isDefEq] ✅️ 0 < ?m.19633 =?= 0 < 1 ▶
[Meta.isDefEq] ✅️ 0 < 1 =?= 0 < 1 ▶
Termination.lean:598:48
[Meta.isDefEq] 💥️ AddZeroClass ?m.19737 =?= AddZeroClass ((i : ?m.19757) → ?m.19758 i) ▶
[Meta.isDefEq] 💥️ LE ?m.19737 =?= LE ((i : ?m.19797) → ?m.19798 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.19737 =?= CanonicallyOrderedAdd (WithTop ?m.19808) ▶
[Meta.isDefEq] ✅️ ?m.19734 ≤ ?m.19735 =?= 0 ≤ ?m.19741 ▶
[Meta.isDefEq] 💥️ AddZeroClass ?m.19737 =?= AddZeroClass ((i : ?m.19835) → ?m.19836 i) ▶
[Meta.isDefEq] 💥️ LE ?m.19737 =?= LE ((i : ?m.19874) → ?m.19875 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.19737 =?= CanonicallyOrderedAdd (WithTop ?m.19884) ▶
[Meta.isDefEq] 💥️ AddZeroClass ?m.19893 =?= AddZeroClass ((i : ?m.21050) → ?m.21051 i) ▶
[Meta.isDefEq] 💥️ LE ?m.19893 =?= LE ((i : ?m.21089) → ?m.21090 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.19893 =?= CanonicallyOrderedAdd (WithTop ?m.21099) ▶
[Meta.isDefEq] 💥️ AddZeroClass ?m.19893 =?= AddZeroClass ((i : ?m.21709) → ?m.21710 i) ▶
[Meta.isDefEq] 💥️ LE ?m.19893 =?= LE ((i : ?m.21748) → ?m.21749 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.19893 =?= CanonicallyOrderedAdd (WithTop ?m.21758) ▶
[Meta.isDefEq] ✅️ AddZeroClass ℕ =?= AddZeroClass ?m.22358 ▶
[Meta.isDefEq] ✅️ ?m.22356 =?= AddMonoid.toAddZeroClass ▶
[Meta.isDefEq] ✅️ AddMonoid ℕ =?= AddMonoid ℕ ▶
[Meta.isDefEq] ✅️ ?m.22359 =?= Nat.instAddMonoid ▶
[Meta.isDefEq] ✅️ ?m.22359 =?= Nat.instAddMonoid ▶
[Meta.isDefEq] ✅️ AddZeroClass ℕ =?= AddZeroClass ℕ
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ AddMonoid ℕ =?= AddMonoid ℕ
[Meta.isDefEq] ✅️ ?m.19738 =?= Nat.instAddMonoid.toAddZeroClass ▶
[Meta.isDefEq] ✅️ LE ℕ =?= LE ℕ
[Meta.isDefEq] ✅️ ?m.22369 =?= instLENat ▶
[Meta.isDefEq] ✅️ LE ℕ =?= LE ℕ
[Meta.isDefEq] ✅️ ?m.19739 =?= instLENat ▶
[Meta.isDefEq] ✅️ CanonicallyOrderedAdd ℕ =?= CanonicallyOrderedAdd ℕ ▶
[Meta.isDefEq] ✅️ ?m.22373 =?= Nat.instCanonicallyOrderedAdd ▶
[Meta.isDefEq] ✅️ CanonicallyOrderedAdd ℕ =?= CanonicallyOrderedAdd ℕ ▶
[Meta.isDefEq] ✅️ ?m.19740 =?= Nat.instCanonicallyOrderedAdd ▶
Termination.lean:598:56
[Meta.isDefEq] ✅️ ?m.19737 =?= ?m.19737
Termination.lean:598:47
[Meta.isDefEq] ✅️ 0 ≤ ?m.19741 =?= 0 ≤ ?m.19741 ▶
Termination.lean:598:31
[Meta.isDefEq] 💥️ Add ?m.19893 =?= Add ((i : ?m.19936) → ?m.19937 i) ▶
[Meta.isDefEq] 💥️ LE ?m.19893 =?= LE ((i : ?m.19976) → ?m.19977 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.19893 ?m.19893 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ 1 ≤ mu (b.recΔ s n) + 1 =?= 1 + 0 ≤ 1 + ?m.19741 ▶
[Meta.isDefEq] 💥️ Add ?m.19893 =?= Add ((i : ?m.20380) → ?m.20381 i) ▶
[Meta.isDefEq] 💥️ LE ?m.19893 =?= LE ((i : ?m.20419) → ?m.20420 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.19893 ?m.19893 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] 💥️ Add ?m.19893 =?= Add ((i : ?m.21142) → ?m.21143 i) ▶
[Meta.isDefEq] 💥️ LE ?m.19893 =?= LE ((i : ?m.21181) → ?m.21182 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.19893 ?m.19893 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] 💥️ Add ?m.19893 =?= Add ((i : ?m.21801) → ?m.21802 i) ▶
[Meta.isDefEq] 💥️ LE ?m.19893 =?= LE ((i : ?m.21840) → ?m.21841 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.19893 ?m.19893 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ Add ℕ =?= Add ℕ
[Meta.isDefEq] ✅️ ?m.22386 =?= instAddNat ▶
[Meta.isDefEq] ✅️ Add ℕ =?= Add ℕ
[Meta.isDefEq] ✅️ ?m.19731 =?= instAddNat ▶
[Meta.isDefEq] ✅️ LE ℕ =?= LE ℕ
[Meta.isDefEq] ✅️ instLENat =?= instLENat
[Meta.isDefEq] ✅️ CovariantClass ℕ ℕ (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ?m.22397 ?m.22397 (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.22394 =?= IsOrderedAddMonoid.toAddLeftMono ▶
[Meta.isDefEq] ✅️ IsOrderedAddMonoid ℕ =?= IsOrderedAddMonoid ℕ ▶
[Meta.isDefEq] ✅️ ?m.22400 =?= Nat.instIsOrderedAddMonoid ▶
[Meta.isDefEq] ✅️ ?m.22400 =?= Nat.instIsOrderedAddMonoid ▶
[Meta.isDefEq] ✅️ CovariantClass ℕ ℕ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 =?= AddLeftMono ℕ ▶
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ AddCommMonoid ℕ =?= AddCommMonoid ℕ
[Meta.isDefEq] ✅️ PartialOrder ℕ =?= PartialOrder ℕ
[Meta.isDefEq] ✅️ IsOrderedAddMonoid ℕ =?= IsOrderedAddMonoid ℕ
[Meta.isDefEq] ✅️ ?m.19733 =?= IsOrderedAddMonoid.toAddLeftMono ▶
Termination.lean:598:59
[Meta.isDefEq] ✅️ ?m.19737 =?= ?m.19893 ▶
[Meta.isDefEq] 💥️ OfNat ?m.19893 1 =?= OfNat ℕ+ ?m.19902 ▶
[Meta.isDefEq] ✅️ ?m.19893 =?= ?m.19893
[Meta.isDefEq] 💥️ OfNat ?m.19893 1 =?= OfNat ℕ+ ?m.21110 ▶
[Meta.isDefEq] 💥️ OfNat ?m.19893 1 =?= OfNat ℕ+ ?m.21769 ▶
[Meta.isDefEq] ✅️ ?m.19894 =?= instOfNatNat ?n ▶
Termination.lean:598:30
Application type mismatch: In the application
lt_of_lt_of_le this (add_le_add_left (zero_le ?m.19741) 1)
the argument
add_le_add_left (zero_le ?m.19741) 1
has type
LE.le.{0} (1 + 0) (1 + ?m.19741) : Prop
but is expected to have type
LE.le.{?u.18934 + 1} 1 (mu (b.recΔ s n) + 1) : Prop
Termination.lean:598:10
[Meta.isDefEq] 💥️ Preorder ?m.19630 =?= Preorder ((i : ?m.19664) → ?m.19665 i) ▶
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= ?m.19632 < ?m.19634 ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18934} =?= Preorder ?m.21024 ▶
[Meta.isDefEq] ✅️ ?m.21022 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.18934} =?= PartialOrder Ordinal.{?u.21034} ▶
[Meta.isDefEq] ✅️ ?m.21025 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.21025 =?= partialOrder ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18934} =?= Preorder Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ Type (?u.18934 + 1) =?= Type (?u.18934 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.18934} =?= PartialOrder Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= 0 < mu (b.recΔ s n) + 1 ▶
Termination.lean:598:30
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.19741 =?= 1 ≤ mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.19741) ⋯ (1 ≤ mu (b.recΔ s n) + 1) =?= CoeT ?m.20974 ?m.20975 ?m.20974 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.19741 =?= 1 ≤ mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.19741) ⋯ (1 ≤ mu (b.recΔ s n) + 1) =?= CoeT ?m.21680 ?m.21681 ?m.21680 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.19741 =?= 1 ≤ mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.19741) ⋯ (1 ≤ mu (b.recΔ s n) + 1) =?= CoeT ?m.22339 ?m.22340 ?m.22339 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.19741 =?= 1 ≤ mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.19741) ⋯ (1 ≤ mu (b.recΔ s n) + 1) =?= CoeT ?m.22651 ?m.22652 ?m.22651 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.19741 =?= 1 ≤ mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.19741) ⋯ (1 ≤ mu (b.recΔ s n) + 1) =?= CoeT ?m.22821 ?m.22822 ?m.22821 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.19741 =?= 1 ≤ mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.19741) ⋯ (1 ≤ mu (b.recΔ s n) + 1) =?= CoeT ?m.22981 ?m.22982 ?m.22981 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.19741 =?= 1 ≤ mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.19741) ⋯ (1 ≤ mu (b.recΔ s n) + 1) =?= CoeT ?m.23141 ?m.23142 ?m.23141 ▶
[Meta.isDefEq] ❌️ 1 + 0 ≤ 1 + ?m.19741 =?= 1 ≤ mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ❌️ LE.le (1 + 0) =?= LE.le 1 ▶
[Meta.isDefEq] 💥️ CoeT (1 + 0 ≤ 1 + ?m.19741) ⋯ (1 ≤ mu (b.recΔ s n) + 1) =?= CoeT ?m.23301 ?m.23302 ?m.23301 ▶
[Meta.isDefEq] ❌️ @LE.le =?= @LE.le ▶
Termination.lean:601:27
[Meta.isDefEq] ✅️ ?m.23320 < ?m.23321 =?= ω ^ 2 < ω ^ 3 ▶
[Meta.isDefEq] ✅️ ω ^ 2 < ω ^ 3 =?= ω ^ 2 < ω ^ 3 ▶
[Meta.isDefEq] ✅️ ?m.24874 < ?m.24875 =?= ω ^ 2 < ω ^ 3 ▶
[Meta.isDefEq] ✅️ ω ^ 2 < ω ^ 3 =?= ω ^ 2 < ω ^ 3 ▶
Termination.lean:600:2
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n
Termination.lean:601:4
[Meta.isDefEq] 💥️ Mul ?m.23315 =?= Mul ((i : ?m.23355) → ?m.23356 i) ▶
[Meta.isDefEq] 💥️ Zero ?m.23315 =?= Zero ((i : ?m.23392) → ?m.23393 i) ▶
[Meta.isDefEq] 💥️ Preorder ?m.23315 =?= Preorder ((i : ?m.23425) → ?m.23426 i) ▶
[Meta.isDefEq] 💥️ PosMulStrictMono ?m.23315 =?= PosMulStrictMono ?m.23433 ▶
[Meta.isDefEq] ✅️ ?m.23312 =?= ?m.23319 _ ?m.23320 < ?m.23319 _ ?m.23321 ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.18934} =?= Mul ?m.23533 ▶
[Meta.isDefEq] ✅️ ?m.23526 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.18934} =?= Distrib ?m.23537 ▶
[Meta.isDefEq] ✅️ ?m.23534 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.18934} =?= NonUnitalNonAssocSemiring ?m.23545 ▶
[Meta.isDefEq] ✅️ ?m.23538 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.18934} =?= NonUnitalNonAssocCommSemiring ?m.23550 ▶
[Meta.isDefEq] ✅️ ?m.23546 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.18934} =?= NonUnitalNonAssocCommRing ?m.23555 ▶
[Meta.isDefEq] ✅️ ?m.23551 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.18934} =?= NonUnitalCommRing ?m.23560 ▶
[Meta.isDefEq] ✅️ ?m.23556 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.18934} =?= CommRing ?m.23565 ▶
[Meta.isDefEq] ✅️ ?m.23561 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.18934} =?= NonUnitalNonAssocSemiring ?m.23567 ▶
[Meta.isDefEq] ✅️ ?m.23538 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.18934} =?= NonUnitalNonAssocRing ?m.23572 ▶
[Meta.isDefEq] ✅️ ?m.23568 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.18934} =?= NonUnitalNonAssocRing ?m.23576 ▶
[Meta.isDefEq] ✅️ ?m.23568 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.18934} =?= NonAssocRing ?m.23579 ▶
[Meta.isDefEq] ✅️ ?m.23577 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.18934} =?= Ring ?m.23585 ▶
[Meta.isDefEq] ✅️ ?m.23580 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.18934} =?= DivisionRing ?m.23588 ▶
[Meta.isDefEq] ✅️ ?m.23586 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.18934} =?= Ring ?m.23590 ▶
[Meta.isDefEq] ✅️ ?m.23580 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.18934} =?= NonUnitalNonAssocRing ?m.23592 ▶
[Meta.isDefEq] ✅️ ?m.23568 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.18934} =?= NonUnitalRing ?m.23596 ▶
[Meta.isDefEq] ✅️ ?m.23593 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.18934} =?= NonUnitalRing ?m.23600 ▶
[Meta.isDefEq] ✅️ ?m.23593 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.18934} =?= NonUnitalNonAssocSemiring ?m.23602 ▶
[Meta.isDefEq] ✅️ ?m.23538 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.18934} =?= NonAssocSemiring ?m.23606 ▶
[Meta.isDefEq] ✅️ ?m.23603 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.18934} =?= Semiring ?m.23613 ▶
[Meta.isDefEq] ✅️ ?m.23607 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.18934} =?= DivisionSemiring ?m.23618 ▶
[Meta.isDefEq] ✅️ ?m.23614 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.18934} =?= Semifield ?m.23621 ▶
[Meta.isDefEq] ✅️ ?m.23619 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.18934} =?= DivisionSemiring ?m.23623 ▶
[Meta.isDefEq] ✅️ ?m.23614 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.18934} =?= Semiring ?m.23625 ▶
[Meta.isDefEq] ✅️ ?m.23607 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.18934} =?= CommSemiring ?m.23629 ▶
[Meta.isDefEq] ✅️ ?m.23626 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.18934} =?= CommSemiring ?m.23631 ▶
[Meta.isDefEq] ✅️ ?m.23626 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.18934} =?= Semiring ?m.23633 ▶
[Meta.isDefEq] ✅️ ?m.23607 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.18934} =?= NonAssocSemiring ?m.23635 ▶
[Meta.isDefEq] ✅️ ?m.23603 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.18934} =?= NonUnitalNonAssocSemiring ?m.23637 ▶
[Meta.isDefEq] ✅️ ?m.23538 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.18934} =?= NonUnitalSemiring ?m.23642 ▶
[Meta.isDefEq] ✅️ ?m.23638 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.18934} =?= NonUnitalCommSemiring ?m.23648 ▶
[Meta.isDefEq] ✅️ ?m.23643 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.18934} =?= NonUnitalCommSemiring ?m.23652 ▶
[Meta.isDefEq] ✅️ ?m.23643 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.18934} =?= NonUnitalSemiring ?m.23654 ▶
[Meta.isDefEq] ✅️ ?m.23638 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.18934} =?= NonUnitalSemiring ?m.23656 ▶
[Meta.isDefEq] ✅️ ?m.23638 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.18934} =?= Mul ?m.23658 ▶
[Meta.isDefEq] ✅️ ?m.23526 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.18934} =?= MulZeroClass ?m.23663 ▶
[Meta.isDefEq] ✅️ ?m.23659 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.18934} =?= MulZeroClass ?m.23667 ▶
[Meta.isDefEq] ✅️ ?m.23659 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.18934} =?= MulZeroOneClass ?m.23671 ▶
[Meta.isDefEq] ✅️ ?m.23668 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.18934} =?= MulZeroOneClass ?m.23675 ▶
[Meta.isDefEq] ✅️ ?m.23668 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.18934} =?= MonoidWithZero Ordinal.{?u.23681} ▶
[Meta.isDefEq] ✅️ ?m.23676 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.23676 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.23668 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.23659 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.18934} =?= Mul Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ Type (?u.18934 + 1) =?= Type (?u.18934 + 1)
[Meta.isDefEq] ✅️ Type (?u.18934 + 1) =?= Type (?u.18934 + 1)
[Meta.isDefEq] ✅️ Type (?u.18934 + 1) =?= Type (?u.18934 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.18934} =?= MonoidWithZero Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.18934} =?= MulZeroOneClass Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.18934} =?= MulZeroClass Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ ?m.23316 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.18934} =?= Zero Ordinal.{?u.23691} ▶
[Meta.isDefEq] ✅️ ?m.23685 =?= zero ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.18934} =?= Zero Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ zero =?= zero
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18934} =?= Preorder Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ❌️ PosMulStrictMono Ordinal.{?u.18934} =?= PosMulStrictMono ?m.23696 ▶
[Meta.isDefEq] ❌️ PosMulStrictMono Ordinal.{?u.18934} =?= PosMulStrictMono ?m.23721 ▶
[Meta.isDefEq] ✅️ PosMulStrictMono Ordinal.{?u.18934} =?= PosMulStrictMono ?m.23897 ▶
[Meta.isDefEq] ✅️ ?m.23692 =?= MulLeftStrictMono.toPosMulStrictMono ▶
[Meta.isDefEq] ✅️ MulLeftStrictMono Ordinal.{?u.18934} =?= CovariantClass ?m.23905 ?m.23905 (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 < x2 ▶
[Meta.isDefEq] ✅️ ?m.23901 =?= IsLeftCancelMul.mulLeftStrictMono*of_mulLeftMono Ordinal.{?u.18934} ▶
[Meta.isDefEq] ✅️ IsLeftCancelMul Ordinal.{?u.18934} =?= IsLeftCancelMul ?m.23928 ▶
[Meta.isDefEq] ✅️ ?m.23907 =?= IsCancelMul.toIsLeftCancelMul ▶
[Meta.isDefEq] ❌️ IsCancelMul Ordinal.{?u.18934} =?= IsCancelMul ?m.23937 ▶
[Meta.isDefEq] ❌️ IsCancelMul Ordinal.{?u.18934} =?= IsCancelMul ?m.24223 ▶
[Meta.isDefEq] ❌️ IsLeftCancelMul Ordinal.{?u.18934} =?= IsLeftCancelMul ?m.24306 ▶
[Meta.isDefEq] ✅️ MulLeftStrictMono Ordinal.{?u.18934} =?= CovariantClass ?m.24365 ?m.24365 ?m.24366 fun x1 x2 => x1 < x2 ▶
[Meta.isDefEq] ✅️ ?m.23901 =?= covariant_lt_of_contravariant_le Ordinal.{?u.18934} fun x1 x2 => x1 * x2 ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.18934} Ordinal.{?u.18934} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.24387 ?m.24387 (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.24368 =?= IsLeftCancelMul.mulLeftReflectLE*of_mulLeftReflectLT Ordinal.{?u.18934} ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.18934} Ordinal.{?u.18934} (fun x1 x2 => x1 * x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.24414 ?m.24414 (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.18934} Ordinal.{?u.18934} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.24654 ?m.24654 (fun x1 x2 => x1 _ x2) ?m.24655 ▶
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 2 <
(mu (b.recΔ s n) + 1) _ ω ^ 3 =?= (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 ▶
[Meta.isDefEq] ✅️ ?m.23312 =?= ?m.24876 _ ?m.24874 < ?m.24876 _ ?m.24875 ▶
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 2 <
(mu (b.recΔ s n) + 1) _ ω ^ 3 =?= (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 ▶
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 2 <
(mu (b.recΔ s n) + 1) _ ω ^ 3 =?= (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 ▶
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 2 <
(mu (b.recΔ s n) + 1) _ ω ^ 3 =?= (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 ▶
Termination.lean:601:36
[Meta.isDefEq] ✅️ 0 < ?m.23319 =?= 0 < mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= 0 < mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ✅️ 0 < ?m.24876 =?= 0 < mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= 0 < mu (b.recΔ s n) + 1 ▶
Termination.lean:603:28
[Meta.isDefEq] ✅️ ?m.24948 < ?m.24949 =?= ω ^ 3 < bigA n ▶
[Meta.isDefEq] ✅️ ?m.25250 < ?m.25251 =?= ω ^ 3 < bigA n ▶
Termination.lean:603:36
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:603:27
[Meta.isDefEq] ✅️ ω ^ 3 < bigA n =?= ω ^ 3 < bigA n ▶
[Meta.isDefEq] ✅️ ω ^ 3 < bigA n =?= ω ^ 3 < bigA n ▶
Termination.lean:602:2
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n
Termination.lean:603:4
[Meta.isDefEq] 💥️ Mul ?m.24943 =?= Mul ((i : ?m.24983) → ?m.24984 i) ▶
[Meta.isDefEq] 💥️ Zero ?m.24943 =?= Zero ((i : ?m.25020) → ?m.25021 i) ▶
[Meta.isDefEq] 💥️ Preorder ?m.24943 =?= Preorder ((i : ?m.25053) → ?m.25054 i) ▶
[Meta.isDefEq] 💥️ PosMulStrictMono ?m.24943 =?= PosMulStrictMono ?m.25061 ▶
[Meta.isDefEq] ✅️ ?m.24940 =?= ?m.24947 _ ?m.24948 < ?m.24947 _ ?m.24949 ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.18934} =?= Mul Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ ?m.24944 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.18934} =?= Zero Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ zero =?= zero
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.18934} =?= Preorder Ordinal.{?u.18934}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 3 <
(mu (b.recΔ s n) + 1) _ bigA n =?= (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n ▶
[Meta.isDefEq] ✅️ ?m.24940 =?= ?m.25252 _ ?m.25250 < ?m.25252 _ ?m.25251 ▶
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 3 <
(mu (b.recΔ s n) + 1) _ bigA n =?= (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n ▶
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 3 <
(mu (b.recΔ s n) + 1) _ bigA n =?= (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n ▶
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 3 <
(mu (b.recΔ s n) + 1) _ bigA n =?= (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n ▶
Termination.lean:603:39
[Meta.isDefEq] ✅️ 0 < ?m.24947 =?= 0 < mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= 0 < mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ✅️ 0 < ?m.25252 =?= 0 < mu (b.recΔ s n) + 1 ▶
[Meta.isDefEq] ✅️ 0 < mu (b.recΔ s n) + 1 =?= 0 < mu (b.recΔ s n) + 1 ▶
Termination.lean:604:17
[Meta.isDefEq] ❌️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416 =?= (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416 ▶
[Meta.isDefEq] ❌️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 2) =?= LT.lt (ω ^ 2 _ (mu (b.recΔ s n) + 1)) ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3) step₁
(ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416) =?= CoeT ?m.28767 ?m.28768 ?m.28767 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416 ▶
[Meta.isDefEq] ❌️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 2) =?= LT.lt (ω ^ 2 _ (mu (b.recΔ s n) + 1)) ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3) step₁
(ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416) =?= CoeT ?m.31935 ?m.31936 ?m.31935 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416 ▶
[Meta.isDefEq] ❌️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 2) =?= LT.lt (ω ^ 2 _ (mu (b.recΔ s n) + 1)) ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3) step₁
(ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416) =?= CoeT ?m.34330 ?m.34331 ?m.34330 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416 ▶
[Meta.isDefEq] ❌️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 2) =?= LT.lt (ω ^ 2 _ (mu (b.recΔ s n) + 1)) ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3) step₁
(ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416) =?= CoeT ?m.36725 ?m.36726 ?m.36725 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3 =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416 ▶
[Meta.isDefEq] ❌️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 2) =?= LT.lt (ω ^ 2 _ (mu (b.recΔ s n) + 1)) ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) _ ω ^ 2 < (mu (b.recΔ s n) + 1) _ ω ^ 3) step₁
(ω ^ 2 _ (mu (b.recΔ s n) + 1) < ?m.25416) =?= CoeT ?m.39120 ?m.39121 ?m.39120 ▶
Termination.lean:604:23
Application type mismatch: In the application
lt*trans ?m.28861 step₂
the argument
step₂
has type
(mu (b.recΔ s n) + 1) * ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n : Prop
but is expected to have type
?m.25416 < bigA n : Prop
Termination.lean:590:0
[diag] Diagnostics ▼
[reduction] unfolded declarations (max: 2593, num: 15): ▶
[reduction] unfolded instances (max: 478, num: 14): ▶
[reduction] unfolded reducible declarations (max: 4248, num: 6): ▶
use set_option diagnostics.threshold <num> to control threshold for reporting counters
Termination.lean:591:51
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n
Termination.lean:604:8
[Meta.isDefEq] 💥️ Preorder ?m.25413 =?= Preorder ((i : ?m.25447) → ?m.25448 i) ▶
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n =?= ?m.25415 < ?m.25417 ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{u*1} =?= Preorder ?m.30153 ▶
[Meta.isDefEq] ✅️ ?m.30151 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{u_1} =?= PartialOrder Ordinal.{?u.30163} ▶
[Meta.isDefEq] ✅️ ?m.30154 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.30154 =?= partialOrder ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{u_1} =?= Preorder Ordinal.{u_1}
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{u_1} =?= PartialOrder Ordinal.{u_1}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ✅️ ω ^ 2 * (mu (b.recΔ s n) + 1) < bigA n =?= ω ^ 2 _ (mu (b.recΔ s n) + 1) < bigA n ▶
Termination.lean:604:23
[Meta.isDefEq] ❌️ ?m.25416 < bigA n =?= (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n =?= ?m.25416 < bigA n ▶
[Meta.isDefEq] ✅️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 3) =?= LT.lt ?m.25416 ▶
[Meta.isDefEq] ❌️ Type ?u.30121 → Type ?u.30122 =?= Ordinal.{u*1} → Prop ▶
[Meta.isDefEq] ❌️ Ordinal.{u_1} =?= Type ?u.30121 ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) * ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n) step₂
(?m.25416 < bigA n) =?= CoeT ?m.30132 ?m.30133 ?m.30132 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n =?= ?m.25416 < bigA n ▶
[Meta.isDefEq] ✅️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 3) =?= LT.lt ?m.25416 ▶
[Meta.isDefEq] ❌️ Type ?u.32547 → Type ?u.32548 =?= Ordinal.{u*1} → Prop ▶
[Meta.isDefEq] ❌️ Ordinal.{u_1} =?= Type ?u.32547 ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) * ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n) step₂
(?m.25416 < bigA n) =?= CoeT ?m.32557 ?m.32558 ?m.32557 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n =?= ?m.25416 < bigA n ▶
[Meta.isDefEq] ✅️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 3) =?= LT.lt ?m.25416 ▶
[Meta.isDefEq] ❌️ Type ?u.34942 → Type ?u.34943 =?= Ordinal.{u*1} → Prop ▶
[Meta.isDefEq] ❌️ Ordinal.{u_1} =?= Type ?u.34942 ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) * ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n) step₂
(?m.25416 < bigA n) =?= CoeT ?m.34952 ?m.34953 ?m.34952 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n =?= ?m.25416 < bigA n ▶
[Meta.isDefEq] ✅️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 3) =?= LT.lt ?m.25416 ▶
[Meta.isDefEq] ❌️ Type ?u.37337 → Type ?u.37338 =?= Ordinal.{u*1} → Prop ▶
[Meta.isDefEq] ❌️ Ordinal.{u_1} =?= Type ?u.37337 ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) * ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n) step₂
(?m.25416 < bigA n) =?= CoeT ?m.37347 ?m.37348 ?m.37347 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n =?= ?m.25416 < bigA n ▶
[Meta.isDefEq] ✅️ LT.lt ((mu (b.recΔ s n) + 1) _ ω ^ 3) =?= LT.lt ?m.25416 ▶
[Meta.isDefEq] ❌️ Type ?u.39732 → Type ?u.39733 =?= Ordinal.{u*1} → Prop ▶
[Meta.isDefEq] ❌️ Ordinal.{u_1} =?= Type ?u.39732 ▶
[Meta.isDefEq] 💥️ CoeT ((mu (b.recΔ s n) + 1) * ω ^ 3 < (mu (b.recΔ s n) + 1) _ bigA n) step₂
(?m.25416 < bigA n) =?= CoeT ?m.39742 ?m.39743 ?m.39742 ▶
[Meta.isDefEq] ✅️ @LT.lt =?= @LT.lt
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ partialOrder.toLT =?= partialOrder.toLT ▶
[Meta.isDefEq] ✅️ (mu (b.recΔ s n) + 1) _ ω ^ 3 =?= ?m.25416 ▶
[Meta.isDefEq] ❌️ (mu (b.recΔ s n) + 1) _ bigA n =?= bigA n ▶
Termination.lean:609:29
[Meta.isDefEq] ✅️ Sort ?u.17671 =?= Type
[Meta.isDefEq] ✅️ Sort ?u.17673 =?= Type
Termination.lean:610:27
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:20
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:29
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:8
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:19
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:7
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:44
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:39
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:46
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:610:4
[Meta.isDefEq] 💥️ Ordinal.{?u.17677} =?= Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17678} x Ordinal.{?u.17677} =?= CoeT ?m.17686 ?m.17687 ?m.17686 ▶
[Meta.isDefEq] ✅️ ?m.17680 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17678} x Ordinal.{?u.17677} =?= CoeT Ordinal.{?u.17678} x Ordinal.{?u.17678} ▶
[Meta.isDefEq] ✅️ Type (?u.17678 + 1) =?= Type (?u.17678 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17678} =?= Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ Ordinal.{?u.17678} =?= Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ Ordinal.{?u.17678} =?= Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ Ordinal.{?u.17678} =?= Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ Ordinal.{?u.17678} =?= ?m.17697 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17678} =?= Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17678} =?= LT ?m.17702 ▶
[Meta.isDefEq] ✅️ ?m.17699 =?= Preorder.toLT ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17678} =?= Preorder ?m.17706 ▶
[Meta.isDefEq] ✅️ ?m.17703 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17678} =?= PartialOrder Ordinal.{?u.17718} ▶
[Meta.isDefEq] ✅️ ?m.17707 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17707 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.17703 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LT Ordinal.{?u.17678} =?= LT Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ Type (?u.17678 + 1) =?= Type (?u.17678 + 1)
[Meta.isDefEq] ✅️ Type (?u.17678 + 1) =?= Type (?u.17678 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17678} =?= PartialOrder Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17678} =?= Preorder Ordinal.{?u.17678}
[Meta.isDefEq] ✅️ ?m.17698 =?= partialOrder.toLT ▶
Termination.lean:610:38
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:612:10
[Meta.isDefEq] ✅️ Sort ?u.17734 =?= Type (?u.17735 + 1)
Termination.lean:612:24
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:612:21
[Meta.isDefEq] 💥️ Ordinal.{?u.17735} =?= Ordinal.{?u.17739}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17739} x Ordinal.{?u.17735} =?= CoeT ?m.17748 ?m.17749 ?m.17748 ▶
[Meta.isDefEq] ✅️ ?m.17742 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17739} x Ordinal.{?u.17735} =?= CoeT Ordinal.{?u.17739} x Ordinal.{?u.17739} ▶
[Meta.isDefEq] ✅️ Type (?u.17739 + 1) =?= Type (?u.17739 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17739} =?= Ordinal.{?u.17739}
[Meta.isDefEq] ✅️ Ordinal.{?u.17739} =?= Ordinal.{?u.17739}
[Meta.isDefEq] 💥️ Ordinal.{?u.17739} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.17739} =?= CoeT ?m.17766 ?m.17767 ?m.17766 ▶
[Meta.isDefEq] ✅️ ?m.17760 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.17739} =?= CoeT Ordinal.{?u.17740} x Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Type ?u.17777 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Type ?u.17778 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.17779) =?= Type (?u.17740 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.17780 =?= HAdd ?m.17783 ?m.17783 ?m.17783 ▶
[Meta.isDefEq] ✅️ ?m.17781 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17797} ▶
[Meta.isDefEq] ✅️ ?m.17784 =?= add ▶
[Meta.isDefEq] ✅️ ?m.17784 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740}
Ordinal.{?u.17740} =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17800 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17801 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.17804 =?= HAdd ?m.17807 ?m.17807 ?m.17807 ▶
[Meta.isDefEq] ✅️ ?m.17805 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17818} ▶
[Meta.isDefEq] ✅️ ?m.17808 =?= add ▶
[Meta.isDefEq] ✅️ ?m.17808 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.17802 =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.17803 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740} ▶
Termination.lean:612:31
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:612:2
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17832 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ mu a + mu b = X =?= ?m.17837 = ?m.17837 ▶
[Meta.isDefEq] ✅️ mu a + mu b = mu a + mu b =?= mu a + mu b = X ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17845 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ mu a + mu b = X =?= ?m.17850 = ?m.17850 ▶
[Meta.isDefEq] ✅️ mu a + mu b = mu a + mu b =?= mu a + mu b = X ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17855 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ mu a + mu b = X =?= ?m.17860 = ?m.17860 ▶
[Meta.isDefEq] ✅️ mu a + mu b = mu a + mu b =?= mu a + mu b = X ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17865 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ mu a + mu b = X =?= ?m.17870 = ?m.17870 ▶
[Meta.isDefEq] ✅️ mu a + mu b = mu a + mu b =?= mu a + mu b = X ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17878 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ X = mu a + mu b =?= ?m.17881 = ?m.17881 ▶
[Meta.isDefEq] ✅️ X = X =?= X = mu a + mu b ▶
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b) ▶
Termination.lean:613:2
[Meta.isDefEq] ✅️ mu a + 1 ≤ X + 1 =?= mu a + 1 ≤ X + 1
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
Termination.lean:613:15
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:613:12
[Meta.isDefEq] ✅️ Type ?u.17967 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Type ?u.17968 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.17969) =?= Type (?u.17740 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740}
Ordinal.{?u.17740} =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17893 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17973 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17974 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.17977 =?= HAdd ?m.17980 ?m.17980 ?m.17980 ▶
[Meta.isDefEq] ✅️ ?m.17978 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17991} ▶
[Meta.isDefEq] ✅️ ?m.17981 =?= add ▶
[Meta.isDefEq] ✅️ ?m.17981 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.17975 =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.17976 =?= instHAdd ▶
Termination.lean:613:19
[Meta.isDefEq] 💥️ OfNat ?m.17893 1 =?= OfNat ℕ+ ?m.17903 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17893 1 =?= OfNat ℕ+ ?m.17914 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17893 1 =?= OfNat ℕ+ ?m.17941 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat ?m.18046 1 ▶
[Meta.isDefEq] ✅️ ?m.18042 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.17740} =?= One Ordinal.{?u.18054} ▶
[Meta.isDefEq] ✅️ ?m.18047 =?= one ▶
[Meta.isDefEq] ✅️ ?m.18047 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat Ordinal.{?u.17740} 1
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.17740} =?= One Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.17895 =?= One.toOfNat1 ▶
Termination.lean:613:12
[Meta.isDefEq] 💥️ Ordinal.{?u.17891} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.17891} =?= CoeT ?m.17959 ?m.17960 ?m.17959 ▶
[Meta.isDefEq] ✅️ ?m.17953 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.17891} =?= CoeT Ordinal.{?u.17740} x Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.18017 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE ?m.18022 ▶
[Meta.isDefEq] ✅️ ?m.18019 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17740} =?= Preorder ?m.18026 ▶
[Meta.isDefEq] ✅️ ?m.18023 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17740} =?= PartialOrder Ordinal.{?u.18038} ▶
[Meta.isDefEq] ✅️ ?m.18027 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18027 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.18023 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17740} =?= PartialOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17740} =?= Preorder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.18018 =?= partialOrder.toLE ▶
Termination.lean:613:23
[Meta.isDefEq] ✅️ Type ?u.17970 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Type ?u.17971 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.17972) =?= Type (?u.17740 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740}
Ordinal.{?u.17740} =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17920 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17995 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.17996 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.17999 =?= HAdd ?m.18002 ?m.18002 ?m.18002 ▶
[Meta.isDefEq] ✅️ ?m.18000 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.18013} ▶
[Meta.isDefEq] ✅️ ?m.18003 =?= add ▶
[Meta.isDefEq] ✅️ ?m.18003 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.17997 =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.17998 =?= instHAdd ▶
Termination.lean:613:27
[Meta.isDefEq] 💥️ OfNat ?m.17920 1 =?= OfNat ℕ+ ?m.17930 ▶
[Meta.isDefEq] 💥️ OfNat ?m.17920 1 =?= OfNat ℕ+ ?m.17950 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat Ordinal.{?u.17740} 1
[Meta.isDefEq] ✅️ ?m.17922 =?= One.toOfNat1 ▶
Termination.lean:614:4
[Meta.isDefEq] ✅️ mu a ≤ X =?= mu a ≤ X
[Meta.isDefEq] ✅️ mu a + 1 ≤ X + 1 =?= mu a + 1 ≤ X + 1
[Meta.isDefEq] ✅️ mu a + 1 ≤ X + 1 =?= mu a + 1 ≤ X + 1 ▶
Termination.lean:614:14
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:614:11
[Meta.isDefEq] 💥️ Ordinal.{?u.18066} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.18066} =?= CoeT ?m.18074 ?m.18075 ?m.18074 ▶
[Meta.isDefEq] ✅️ ?m.18068 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.18066} =?= CoeT Ordinal.{?u.17740} x Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.18082 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.18083 =?= partialOrder.toLE ▶
Termination.lean:614:37
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu a ≤ mu a + mu b ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu a ≤ mu a + mu b ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu a ≤ mu a + mu b ▶
[Meta.isDefEq] ❌️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.18247 ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.18249 ▶
[Meta.isDefEq] ✅️ ?m.18244 =?= Unique.instSubsingleton ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.18251 ▶
[Meta.isDefEq] ✅️ ?m.18244 =?= IsEmpty.instSubsingleton ▶
[Meta.isDefEq] ✅️ ?a ≤ ?a + ?b =?= mu a ≤ mu a + mu b ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass Ordinal.{?u.18327} Ordinal.{?u.18327} (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.18324 =?= instAddLeftMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddLeftMono Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddLeftMono ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass Ordinal.{?u.18449} Ordinal.{?u.18449} (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.18445 =?= instAddLeftReflectLE ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddLeftReflectLE Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddLeftReflectLE ▶
[Meta.Tactic.simp.rewrite] le_add_iff_nonneg_right:1000:
mu a ≤ mu a + mu b
==>
0 ≤ mu b
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= 0 ≤ mu b ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= 0 ≤ mu b ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= 0 ≤ mu b ▶
[Meta.isDefEq] ✅️ 0 ≤ ?a =?= 0 ≤ mu b ▶
[Meta.isDefEq] ✅️ CanonicallyOrderedAdd Ordinal.{?u.17740} =?= CanonicallyOrderedAdd Ordinal.{?u.18632} ▶
[Meta.isDefEq] ✅️ ?m.18631 =?= canonicallyOrderedAdd ▶
[Meta.isDefEq] ✅️ CanonicallyOrderedAdd Ordinal.{?u.17740} =?= CanonicallyOrderedAdd Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= canonicallyOrderedAdd ▶
[Meta.Tactic.simp.rewrite] zero_le:1000:
0 ≤ mu b
==>
True
[Meta.isDefEq] ✅️ ?p = True =?= (mu a ≤ mu a + mu b) = True ▶
Termination.lean:615:11
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?a =?= ?b ▶
[Meta.isDefEq] ✅️ ?b =?= ?b
Termination.lean:615:21
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?a =?= ?b ▶
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?b =?= ?b
[Meta.isDefEq] ✅️ ?c =?= ?c
Termination.lean:615:36
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
Termination.lean:615:70
[Meta.isDefEq] ✅️ ?m.20087 ≤ ?m.20088 =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ mu a ≤ X =?= mu a ≤ X ▶
Termination.lean:615:4
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu a + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu a + 1
==>
Order.succ (mu a)
[Meta.isDefEq] ❌️ ?a + ?b =?= X + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= X + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
X + 1
==>
Order.succ X
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ❌️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.19386 ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.19388 ▶
[Meta.isDefEq] ✅️ ?m.19383 =?= Unique.instSubsingleton ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.19390 ▶
[Meta.isDefEq] ✅️ ?m.19383 =?= IsEmpty.instSubsingleton ▶
[Meta.isDefEq] ❌️ Order.succ ?a ≤ ?a =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ Order.succ ?a ≤ ?b =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.19489} ▶
[Meta.isDefEq] ✅️ ?m.19484 =?= instNoMaxOrder ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.Tactic.simp.rewrite] Order.succ_le_iff:1000:
Order.succ (mu a) ≤ Order.succ X
==>
mu a < Order.succ X
[Meta.isDefEq] ✅️ ?x > ?y =?= mu a < Order.succ X ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= mu a < Order.succ X ▶
[Meta.isDefEq] ❌️ ?a < Order.succ ?a =?= mu a < Order.succ X ▶
[Meta.isDefEq] ✅️ ?a < Order.succ ?b =?= mu a < Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu a ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu a ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?a < Order.succ ?b =?= mu a < Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.19957} ▶
[Meta.isDefEq] ✅️ ?m.19952 =?= instNoMaxOrder ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.Tactic.simp.rewrite] Order.lt_succ_iff:1000:
mu a < Order.succ X
==>
mu a ≤ X
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu a ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu a ≤ X ▶
[Meta.Tactic.simp.rewrite] ge_iff_le:1000:
mu a ≤ X
==>
mu a ≤ X
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu a + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu a + 1
==>
Order.succ (mu a)
[Meta.isDefEq] ❌️ ?a + ?b =?= X + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= X + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
X + 1
==>
Order.succ X
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ❌️ Order.succ ?a ≤ ?a =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ Order.succ ?a ≤ ?b =?= Order.succ (mu a) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.Tactic.simp.rewrite] Order.succ_le_iff:1000:
Order.succ (mu a) ≤ Order.succ X
==>
mu a < Order.succ X
[Meta.isDefEq] ✅️ ?x > ?y =?= mu a < Order.succ X ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= mu a < Order.succ X ▶
[Meta.isDefEq] ❌️ ?a < Order.succ ?a =?= mu a < Order.succ X ▶
[Meta.isDefEq] ✅️ ?a < Order.succ ?b =?= mu a < Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu a ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu a ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?a < Order.succ ?b =?= mu a < Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.Tactic.simp.rewrite] Order.lt_succ_iff:1000:
mu a < Order.succ X
==>
mu a ≤ X
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu a ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu a ≤ X ▶
[Meta.isDefEq] ✅️ mu a ≤ X =?= mu a ≤ X
[Meta.isDefEq] ✅️ mu a ≤ X =?= mu a ≤ X
Termination.lean:615:53
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.20144} ▶
[Meta.isDefEq] ✅️ ?m.20137 =?= add ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.20084 =?= add ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE ?m.20149 ▶
[Meta.isDefEq] ✅️ ?m.20146 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17740} =?= Preorder ?m.20153 ▶
[Meta.isDefEq] ✅️ ?m.20150 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17740} =?= PartialOrder Ordinal.{?u.20165} ▶
[Meta.isDefEq] ✅️ ?m.20154 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.20154 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.20150 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17740} =?= PartialOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17740} =?= Preorder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.20174} Ordinal.{?u.20174} (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.20173} Ordinal.{?u.20173} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.20167 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?m.20086 =?= instAddRightMono ▶
Termination.lean:615:75
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.20118 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat ?m.20124 1 ▶
[Meta.isDefEq] ✅️ ?m.20120 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.17740} =?= One Ordinal.{?u.20132} ▶
[Meta.isDefEq] ✅️ ?m.20125 =?= one ▶
[Meta.isDefEq] ✅️ ?m.20125 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat Ordinal.{?u.17740} 1
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.17740} =?= One Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.20119 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
Termination.lean:616:2
[Meta.isDefEq] ✅️ mu b + 1 ≤ X + 1 =?= mu b + 1 ≤ X + 1
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
Termination.lean:616:15
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:616:12
[Meta.isDefEq] ✅️ Type ?u.21281 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Type ?u.21282 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.21283) =?= Type (?u.17740 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.21284 =?= HAdd ?m.21287 ?m.21287 ?m.21287 ▶
[Meta.isDefEq] ✅️ ?m.21285 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.21301} ▶
[Meta.isDefEq] ✅️ ?m.21288 =?= add ▶
[Meta.isDefEq] ✅️ ?m.21288 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740}
Ordinal.{?u.17740} =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.21204 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.21306 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.21307 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.21310 =?= HAdd ?m.21313 ?m.21313 ?m.21313 ▶
[Meta.isDefEq] ✅️ ?m.21311 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.21324} ▶
[Meta.isDefEq] ✅️ ?m.21314 =?= add ▶
[Meta.isDefEq] ✅️ ?m.21314 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.21308 =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.21309 =?= instHAdd ▶
Termination.lean:616:19
[Meta.isDefEq] 💥️ OfNat ?m.21204 1 =?= OfNat ℕ+ ?m.21214 ▶
[Meta.isDefEq] 💥️ OfNat ?m.21204 1 =?= OfNat ℕ+ ?m.21225 ▶
[Meta.isDefEq] 💥️ OfNat ?m.21204 1 =?= OfNat ℕ+ ?m.21252 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat Ordinal.{?u.17740} 1
[Meta.isDefEq] ✅️ ?m.21206 =?= One.toOfNat1 ▶
Termination.lean:616:12
[Meta.isDefEq] 💥️ Ordinal.{?u.21202} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.21202} =?= CoeT ?m.21270 ?m.21271 ?m.21270 ▶
[Meta.isDefEq] ✅️ ?m.21264 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.21202} =?= CoeT Ordinal.{?u.17740} x Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.21353 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.21354 =?= partialOrder.toLE ▶
Termination.lean:616:23
[Meta.isDefEq] ✅️ Type ?u.21303 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Type ?u.21304 =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.21305) =?= Type (?u.17740 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740}
Ordinal.{?u.17740} =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.21231 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.21331 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.21332 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.21335 =?= HAdd ?m.21338 ?m.21338 ?m.21338 ▶
[Meta.isDefEq] ✅️ ?m.21336 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.21349} ▶
[Meta.isDefEq] ✅️ ?m.21339 =?= add ▶
[Meta.isDefEq] ✅️ ?m.21339 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} ?m.21333 =?= HAdd Ordinal.{?u.17740} Ordinal.{?u.17740} Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.21334 =?= instHAdd ▶
Termination.lean:616:27
[Meta.isDefEq] 💥️ OfNat ?m.21231 1 =?= OfNat ℕ+ ?m.21241 ▶
[Meta.isDefEq] 💥️ OfNat ?m.21231 1 =?= OfNat ℕ+ ?m.21261 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat Ordinal.{?u.17740} 1
[Meta.isDefEq] ✅️ ?m.21233 =?= One.toOfNat1 ▶
Termination.lean:617:4
[Meta.isDefEq] ✅️ mu b ≤ X =?= mu b ≤ X
[Meta.isDefEq] ✅️ mu b + 1 ≤ X + 1 =?= mu b + 1 ≤ X + 1
[Meta.isDefEq] ✅️ mu b + 1 ≤ X + 1 =?= mu b + 1 ≤ X + 1 ▶
Termination.lean:617:14
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:617:11
[Meta.isDefEq] 💥️ Ordinal.{?u.21362} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.21362} =?= CoeT ?m.21370 ?m.21371 ?m.21370 ▶
[Meta.isDefEq] ✅️ ?m.21364 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.21362} =?= CoeT Ordinal.{?u.17740} x Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.21378 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.21379 =?= partialOrder.toLE ▶
Termination.lean:617:61
[Meta.isDefEq] ✅️ ?m.25522 ≤ ?m.25524 =?= ?m.25522 ≤ ?m.25524
[Meta.isDefEq] ✅️ Ordinal.{?u.25516} =?= Ordinal.{?u.25516}
Termination.lean:617:37
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu b ≤ mu a + mu b ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu b ≤ mu a + mu b ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu b ≤ mu a + mu b ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= mu b ≤ mu a + mu b ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b + ?a =?= mu b ≤ mu a + mu b ▶
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.21663} Ordinal.{?u.21663} (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.21662} Ordinal.{?u.21662} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.21656 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.21830 ?m.21830 (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.21823 =?= IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ IsRightCancelAdd Ordinal.{?u.17740} =?= IsRightCancelAdd ?m.21869 ▶
[Meta.isDefEq] ✅️ ?m.21832 =?= IsCancelAdd.toIsRightCancelAdd ▶
[Meta.isDefEq] ❌️ IsCancelAdd Ordinal.{?u.17740} =?= IsCancelAdd ?m.21878 ▶
[Meta.isDefEq] ❌️ IsCancelAdd Ordinal.{?u.17740} =?= IsCancelAdd ?m.22311 ▶
[Meta.isDefEq] ❌️ IsRightCancelAdd Ordinal.{?u.17740} =?= IsRightCancelAdd ?m.22573 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.22729 ?m.22729 (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.23009 ?m.23009 (Function.swap fun x1 x2 => x1 + x2) ?m.23010 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.23824 ?m.23824 (Function.swap fun x1 x2 => x1 _ x2) ?m.23825 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.23924 ?m.23924 (Function.swap fun x1 x2 => x1 + x2) ?m.23925 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.25186 ?m.25186 (Function.swap fun x1 x2 => x1 _ x2) ?m.25187 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= mu b ≤ mu a + mu b ▶
[Meta.isDefEq] ❌️ ?a ≤ ?b + ?a =?= mu b ≤ mu a + mu b ▶
[Meta.isDefEq] ❌️ fun as => Array.filterMap some as =?= ?m.25615 ▶
[Meta.isDefEq] ❌️ fun as => Array.filterMap some as =?= ?m.25616 ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= ?m.25615 ≤ ?m.25616 + ?m.25615 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= ?m.25615 ≤ ?m.25616 + ?m.25615 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= ?m.25615 ≤ ?m.25616 + ?m.25615 ▶
[Meta.isDefEq] ❌️ Subsingleton Ordinal.{?u.25516} =?= Subsingleton ?m.25780 ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.25516} =?= Subsingleton ?m.25782 ▶
[Meta.isDefEq] ✅️ ?m.25777 =?= Unique.instSubsingleton ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.25516} =?= Subsingleton ?m.25784 ▶
[Meta.isDefEq] ✅️ ?m.25777 =?= IsEmpty.instSubsingleton ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= ?m.25615 ≤ ?m.25616 + ?m.25615 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b + ?a =?= ?m.25615 ≤ ?m.25616 + ?m.25615 ▶
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.25963} Ordinal.{?u.25963} (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.25962} Ordinal.{?u.25962} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.25956 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.25516} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ ContravariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.26168 ?m.26168 (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.26161 =?= IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT Ordinal.{?u.25516} ▶
[Meta.isDefEq] ✅️ IsRightCancelAdd Ordinal.{?u.25516} =?= IsRightCancelAdd ?m.26209 ▶
[Meta.isDefEq] ✅️ ?m.26170 =?= IsCancelAdd.toIsRightCancelAdd ▶
[Meta.isDefEq] ❌️ IsCancelAdd Ordinal.{?u.25516} =?= IsCancelAdd ?m.26218 ▶
[Meta.isDefEq] ❌️ IsCancelAdd Ordinal.{?u.25516} =?= IsCancelAdd ?m.26714 ▶
[Meta.isDefEq] ❌️ IsRightCancelAdd Ordinal.{?u.25516} =?= IsRightCancelAdd ?m.26976 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.27132 ?m.27132 (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.27412 ?m.27412 (Function.swap fun x1 x2 => x1 + x2) ?m.27413 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.28229 ?m.28229 (Function.swap fun x1 x2 => x1 _ x2) ?m.28230 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.28329 ?m.28329 (Function.swap fun x1 x2 => x1 + x2) ?m.28330 ▶
[Meta.isDefEq] ❌️ ContravariantClass Ordinal.{?u.25516} Ordinal.{?u.25516} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= ContravariantClass ?m.29591 ?m.29591 (Function.swap fun x1 x2 => x1 _ x2) ?m.29592 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a + ?b =?= ?m.25615 ≤ ?m.25616 + ?m.25615 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?b + ?a =?= ?m.25615 ≤ ?m.25616 + ?m.25615 ▶
[Meta.isDefEq] ✅️ mu b ≤ mu a + mu b =?= ?m.25615 ≤ ?m.25616 + ?m.25615 ▶
[Meta.isDefEq] ✅️ mu b ≤ mu a + mu b =?= mu b ≤ mu a + mu b ▶
Termination.lean:617:49
[Meta.isDefEq] 💥️ AddCommMagma ?m.25518 =?= AddCommMagma ?m.25529ᵐᵒᵖ ▶
[Meta.isDefEq] 💥️ Preorder ?m.25518 =?= Preorder ((i : ?m.25561) → ?m.25562 i) ▶
[Meta.isDefEq] 💥️ CanonicallyOrderedAdd ?m.25518 =?= CanonicallyOrderedAdd (WithTop ?m.25572) ▶
[Meta.isDefEq] ✅️ CoeFun (?m.25522 ≤ ?m.25523 + ?m.25524) ?m.25581 =?= CoeFun ?m.25586 fun x => (a : ?m.25587) → ?m.25588 a ▶
[Meta.isDefEq] ✅️ ?m.25582 =?= DFunLike.hasCoeToFun ▶
[Meta.isDefEq] ✅️ DFunLike (?m.25522 ≤ ?m.25523 + ?m.25524) ?m.25587 ?m.25588 =?= DFunLike ?m.25604 ?m.25605 fun x => ?m.25606 ▶
[Meta.isDefEq] ✅️ ?m.25589 =?= EquivLike.toFunLike ▶
Termination.lean:617:63
[Meta.isDefEq] ✅️ Ordinal.{?u.25516} =?= Ordinal.{?u.25516}
Termination.lean:618:11
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?a =?= ?b ▶
[Meta.isDefEq] ✅️ ?b =?= ?b
Termination.lean:618:21
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?a =?= ?b ▶
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?b =?= ?b
[Meta.isDefEq] ✅️ ?c =?= ?c
Termination.lean:618:36
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
Termination.lean:618:70
[Meta.isDefEq] ✅️ ?m.31624 ≤ ?m.31625 =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ mu b ≤ X =?= mu b ≤ X ▶
Termination.lean:618:4
[Meta.isDefEq] ❌️ ?a + ?b =?= mu b + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu b + 1 ▶
[Meta.Tactic.simp.rewrite] add*one_eq_succ:1000:
mu b + 1
==>
Order.succ (mu b)
[Meta.isDefEq] ❌️ ?a + ?b =?= X + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= X + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
X + 1
==>
Order.succ X
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ❌️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.30923 ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.30925 ▶
[Meta.isDefEq] ✅️ ?m.30920 =?= Unique.instSubsingleton ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.17740} =?= Subsingleton ?m.30927 ▶
[Meta.isDefEq] ✅️ ?m.30920 =?= IsEmpty.instSubsingleton ▶
[Meta.isDefEq] ❌️ Order.succ ?a ≤ ?a =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ Order.succ ?a ≤ ?b =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.31026} ▶
[Meta.isDefEq] ✅️ ?m.31021 =?= instNoMaxOrder ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.Tactic.simp.rewrite] Order.succ_le_iff:1000:
Order.succ (mu b) ≤ Order.succ X
==>
mu b < Order.succ X
[Meta.isDefEq] ✅️ ?x > ?y =?= mu b < Order.succ X ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= mu b < Order.succ X ▶
[Meta.isDefEq] ❌️ ?a < Order.succ ?a =?= mu b < Order.succ X ▶
[Meta.isDefEq] ✅️ ?a < Order.succ ?b =?= mu b < Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu b ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu b ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?a < Order.succ ?b =?= mu b < Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.31494} ▶
[Meta.isDefEq] ✅️ ?m.31489 =?= instNoMaxOrder ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.Tactic.simp.rewrite] Order.lt_succ_iff:1000:
mu b < Order.succ X
==>
mu b ≤ X
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu b ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu b ≤ X ▶
[Meta.Tactic.simp.rewrite] ge_iff_le:1000:
mu b ≤ X
==>
mu b ≤ X
[Meta.isDefEq] ❌️ ?a + ?b =?= mu b + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu b + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu b + 1
==>
Order.succ (mu b)
[Meta.isDefEq] ❌️ ?a + ?b =?= X + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= X + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
X + 1
==>
Order.succ X
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ❌️ Order.succ ?a ≤ ?a =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ Order.succ ?a ≤ ?b =?= Order.succ (mu b) ≤ Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.Tactic.simp.rewrite] Order.succ_le_iff:1000:
Order.succ (mu b) ≤ Order.succ X
==>
mu b < Order.succ X
[Meta.isDefEq] ✅️ ?x > ?y =?= mu b < Order.succ X ▶
[Meta.isDefEq] ❌️ ?x < ?x =?= mu b < Order.succ X ▶
[Meta.isDefEq] ❌️ ?a < Order.succ ?a =?= mu b < Order.succ X ▶
[Meta.isDefEq] ✅️ ?a < Order.succ ?b =?= mu b < Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu b ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu b ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?a < Order.succ ?b =?= mu b < Order.succ X ▶
[Meta.isDefEq] ✅️ NoMaxOrder Ordinal.{?u.17740} =?= NoMaxOrder Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= instNoMaxOrder ▶
[Meta.Tactic.simp.rewrite] Order.lt_succ_iff:1000:
mu b < Order.succ X
==>
mu b ≤ X
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= mu b ≤ X ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= mu b ≤ X ▶
[Meta.isDefEq] ✅️ mu b ≤ X =?= mu b ≤ X
[Meta.isDefEq] ✅️ mu b ≤ X =?= mu b ≤ X
Termination.lean:618:53
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.31681} ▶
[Meta.isDefEq] ✅️ ?m.31674 =?= add ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.17740} =?= Add Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.31621 =?= add ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE ?m.31686 ▶
[Meta.isDefEq] ✅️ ?m.31683 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17740} =?= Preorder ?m.31690 ▶
[Meta.isDefEq] ✅️ ?m.31687 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17740} =?= PartialOrder Ordinal.{?u.31702} ▶
[Meta.isDefEq] ✅️ ?m.31691 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.31691 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.31687 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.17740} =?= LE Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.17740} =?= PartialOrder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.17740} =?= Preorder Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.31711} Ordinal.{?u.31711} (Function.swap fun x1 x2 => x1 * x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.31710} Ordinal.{?u.31710} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.31704 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.17740} Ordinal.{?u.17740} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ ?m.31623 =?= instAddRightMono ▶
Termination.lean:618:75
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= ?m.31655 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat ?m.31661 1 ▶
[Meta.isDefEq] ✅️ ?m.31657 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.17740} =?= One Ordinal.{?u.31669} ▶
[Meta.isDefEq] ✅️ ?m.31662 =?= one ▶
[Meta.isDefEq] ✅️ ?m.31662 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.17740} 1 =?= OfNat Ordinal.{?u.17740} 1
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.17740} =?= One Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ ?m.31656 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
Termination.lean:619:2
[Meta.isDefEq] ✅️ mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) =?= mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1)
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
Termination.lean:620:17
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:620:10
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:620:19
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:620:9
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:621:8
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33153 ▶
[Meta.isDefEq] ✅️ ?m.32748 =?= ?m.33154 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33154 ?m.33157 =?= HPow ?m.33162 ?m.33163 ?m.33162 ▶
[Meta.isDefEq] ✅️ ?m.33158 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33154 =?= Pow Ordinal.{?u.33179} Ordinal.{?u.33179} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33154 ?m.33370 =?= HPow ?m.33375 ?m.33376 ?m.33375 ▶
[Meta.isDefEq] ✅️ ?m.33371 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33154 =?= Pow Ordinal.{?u.33389} Ordinal.{?u.33389} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33154 ?m.33460 =?= HPow ?m.33465 ?m.33466 ?m.33465 ▶
[Meta.isDefEq] ✅️ ?m.33461 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33154 =?= Pow Ordinal.{?u.33476} Ordinal.{?u.33476} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33154 ?m.33532 =?= HPow ?m.33537 ?m.33538 ?m.33537 ▶
[Meta.isDefEq] ✅️ ?m.33533 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33154 =?= Pow Ordinal.{?u.33548} Ordinal.{?u.33548} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33154 ?m.33604 =?= HPow ?m.33609 ?m.33610 ?m.33609 ▶
[Meta.isDefEq] ✅️ ?m.33605 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33154 =?= Pow Ordinal.{?u.33620} Ordinal.{?u.33620} ▶
[Meta.isDefEq] ✅️ ?m.33156 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?β =?= Pow Ordinal.{?u.33677} Ordinal.{?u.33677} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.32788} =?= Monoid Ordinal.{?u.33691} ▶
[Meta.isDefEq] ✅️ ?m.33685 =?= monoid ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.32788} =?= Monoid Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:621:17
[Meta.isDefEq] 💥️ OfNat ?m.32748 3 =?= OfNat ℕ+ ?m.32757 ▶
[Meta.isDefEq] 💥️ OfNat ?m.32748 3 =?= OfNat ℕ+ ?m.32842 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33154 3 =?= OfNat ℕ+ ?m.33339 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33154 3 =?= OfNat ℕ+ ?m.33450 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33154 3 =?= OfNat ℕ+ ?m.33522 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33154 3 =?= OfNat ℕ+ ?m.33594 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ ?m.33697 ▶
[Meta.isDefEq] ✅️ ?m.33694 =?= instOfNatNat 3 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ 3
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ?m.32750 =?= instOfNatNat 3 ▶
Termination.lean:621:22
[Meta.isDefEq] ✅️ Type ?u.33141 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type ?u.33142 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.33143) =?= Type (?u.32788 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788}
Ordinal.{?u.32788} =?= HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.32765 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33182 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33183 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.33186 =?= HAdd ?m.33189 ?m.33189 ?m.33189 ▶
[Meta.isDefEq] ✅️ ?m.33187 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.32788} =?= Add Ordinal.{?u.33200} ▶
[Meta.isDefEq] ✅️ ?m.33190 =?= add ▶
[Meta.isDefEq] ✅️ ?m.33190 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.33184 =?= HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788} ▶
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.32788} =?= Add Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33185 =?= instHAdd ▶
Termination.lean:621:26
[Meta.isDefEq] 💥️ OfNat ?m.32765 1 =?= OfNat ℕ+ ?m.32775 ▶
[Meta.isDefEq] 💥️ OfNat ?m.32765 1 =?= OfNat ℕ+ ?m.32851 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.32788} 1 =?= OfNat ?m.33347 1 ▶
[Meta.isDefEq] ✅️ ?m.33343 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.32788} =?= One Ordinal.{?u.33355} ▶
[Meta.isDefEq] ✅️ ?m.33348 =?= one ▶
[Meta.isDefEq] ✅️ ?m.33348 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.32788} 1 =?= OfNat Ordinal.{?u.32788} 1
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.32788} =?= One Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.32767 =?= One.toOfNat1 ▶
Termination.lean:621:8
[Meta.isDefEq] ✅️ Type ?u.32956 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type ?u.32957 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.32958) =?= Type (?u.32788 + 1) ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.32959 =?= HMul ?m.32962 ?m.32962 ?m.32962 ▶
[Meta.isDefEq] ✅️ ?m.32960 =?= instHMul ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul ?m.32976 ▶
[Meta.isDefEq] ✅️ ?m.32963 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.32788} =?= Distrib ?m.32981 ▶
[Meta.isDefEq] ✅️ ?m.32977 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.32989 ▶
[Meta.isDefEq] ✅️ ?m.32982 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocCommSemiring ?m.32994 ▶
[Meta.isDefEq] ✅️ ?m.32990 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.32788} =?= NonUnitalNonAssocCommRing ?m.32999 ▶
[Meta.isDefEq] ✅️ ?m.32995 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.32788} =?= NonUnitalCommRing ?m.33004 ▶
[Meta.isDefEq] ✅️ ?m.33000 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.32788} =?= CommRing ?m.33009 ▶
[Meta.isDefEq] ✅️ ?m.33005 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.33013 ▶
[Meta.isDefEq] ✅️ ?m.32982 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.33018 ▶
[Meta.isDefEq] ✅️ ?m.33014 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.33022 ▶
[Meta.isDefEq] ✅️ ?m.33014 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.32788} =?= NonAssocRing ?m.33025 ▶
[Meta.isDefEq] ✅️ ?m.33023 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.32788} =?= Ring ?m.33031 ▶
[Meta.isDefEq] ✅️ ?m.33026 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.32788} =?= DivisionRing ?m.33036 ▶
[Meta.isDefEq] ✅️ ?m.33032 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.32788} =?= Ring ?m.33040 ▶
[Meta.isDefEq] ✅️ ?m.33026 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.33042 ▶
[Meta.isDefEq] ✅️ ?m.33014 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.32788} =?= NonUnitalRing ?m.33046 ▶
[Meta.isDefEq] ✅️ ?m.33043 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.32788} =?= NonUnitalRing ?m.33050 ▶
[Meta.isDefEq] ✅️ ?m.33043 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.33052 ▶
[Meta.isDefEq] ✅️ ?m.32982 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.32788} =?= NonAssocSemiring ?m.33056 ▶
[Meta.isDefEq] ✅️ ?m.33053 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.33063 ▶
[Meta.isDefEq] ✅️ ?m.33057 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.32788} =?= DivisionSemiring ?m.33069 ▶
[Meta.isDefEq] ✅️ ?m.33064 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.32788} =?= Semifield ?m.33074 ▶
[Meta.isDefEq] ✅️ ?m.33070 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.32788} =?= DivisionSemiring ?m.33078 ▶
[Meta.isDefEq] ✅️ ?m.33064 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.33080 ▶
[Meta.isDefEq] ✅️ ?m.33057 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.32788} =?= CommSemiring ?m.33084 ▶
[Meta.isDefEq] ✅️ ?m.33081 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.32788} =?= CommSemiring ?m.33088 ▶
[Meta.isDefEq] ✅️ ?m.33081 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.33090 ▶
[Meta.isDefEq] ✅️ ?m.33057 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.32788} =?= NonAssocSemiring ?m.33092 ▶
[Meta.isDefEq] ✅️ ?m.33053 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.33094 ▶
[Meta.isDefEq] ✅️ ?m.32982 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.33099 ▶
[Meta.isDefEq] ✅️ ?m.33095 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.32788} =?= NonUnitalCommSemiring ?m.33105 ▶
[Meta.isDefEq] ✅️ ?m.33100 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.32788} =?= NonUnitalCommSemiring ?m.33109 ▶
[Meta.isDefEq] ✅️ ?m.33100 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.33111 ▶
[Meta.isDefEq] ✅️ ?m.33095 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.33113 ▶
[Meta.isDefEq] ✅️ ?m.33095 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul ?m.33115 ▶
[Meta.isDefEq] ✅️ ?m.32963 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass ?m.33120 ▶
[Meta.isDefEq] ✅️ ?m.33116 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass ?m.33124 ▶
[Meta.isDefEq] ✅️ ?m.33116 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass ?m.33128 ▶
[Meta.isDefEq] ✅️ ?m.33125 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass ?m.33132 ▶
[Meta.isDefEq] ✅️ ?m.33125 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.32788} =?= MonoidWithZero Ordinal.{?u.33138} ▶
[Meta.isDefEq] ✅️ ?m.33133 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.33133 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.33125 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.33116 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ ?m.32963 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.32788} Ordinal.{?u.32788}
Ordinal.{?u.32788} =?= HMul Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.32788} =?= MonoidWithZero Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33155 =?= ?m.33207 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33208 ▶
[Meta.isDefEq] 💥️ HMul ?m.33207 Ordinal.{?u.32788} ?m.33211 =?= HMul ?m.33216 ?m.33216 ?m.33216 ▶
[Meta.isDefEq] 💥️ HMul ?m.33207 Ordinal.{?u.32788} ?m.33390 =?= HMul ?m.33395 ?m.33395 ?m.33395 ▶
[Meta.isDefEq] 💥️ HMul ?m.33207 Ordinal.{?u.32788} ?m.33477 =?= HMul ?m.33482 ?m.33482 ?m.33482 ▶
[Meta.isDefEq] 💥️ HMul ?m.33207 Ordinal.{?u.32788} ?m.33549 =?= HMul ?m.33554 ?m.33554 ?m.33554 ▶
[Meta.isDefEq] 💥️ HMul ?m.33207 Ordinal.{?u.32788} ?m.33621 =?= HMul ?m.33626 ?m.33626 ?m.33626 ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.33710 =?= HMul ?m.33713 ?m.33713 ?m.33713 ▶
[Meta.isDefEq] ✅️ ?m.33711 =?= instHMul ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul ?m.33724 ▶
[Meta.isDefEq] ✅️ ?m.33714 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.32788} =?= Distrib ?m.33727 ▶
[Meta.isDefEq] ✅️ ?m.33725 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.33733 ▶
[Meta.isDefEq] ✅️ ?m.33728 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocCommSemiring ?m.33736 ▶
[Meta.isDefEq] ✅️ ?m.33734 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.32788} =?= NonUnitalNonAssocCommRing ?m.33739 ▶
[Meta.isDefEq] ✅️ ?m.33737 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.32788} =?= NonUnitalCommRing ?m.33742 ▶
[Meta.isDefEq] ✅️ ?m.33740 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.32788} =?= CommRing ?m.33745 ▶
[Meta.isDefEq] ✅️ ?m.33743 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.33747 ▶
[Meta.isDefEq] ✅️ ?m.33728 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.33752 ▶
[Meta.isDefEq] ✅️ ?m.33748 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.33754 ▶
[Meta.isDefEq] ✅️ ?m.33748 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.32788} =?= NonAssocRing ?m.33757 ▶
[Meta.isDefEq] ✅️ ?m.33755 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.32788} =?= Ring ?m.33761 ▶
[Meta.isDefEq] ✅️ ?m.33758 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.32788} =?= DivisionRing ?m.33764 ▶
[Meta.isDefEq] ✅️ ?m.33762 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.32788} =?= Ring ?m.33766 ▶
[Meta.isDefEq] ✅️ ?m.33758 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.33768 ▶
[Meta.isDefEq] ✅️ ?m.33748 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.32788} =?= NonUnitalRing ?m.33772 ▶
[Meta.isDefEq] ✅️ ?m.33769 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.32788} =?= NonUnitalRing ?m.33774 ▶
[Meta.isDefEq] ✅️ ?m.33769 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.33776 ▶
[Meta.isDefEq] ✅️ ?m.33728 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.32788} =?= NonAssocSemiring ?m.33780 ▶
[Meta.isDefEq] ✅️ ?m.33777 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.33785 ▶
[Meta.isDefEq] ✅️ ?m.33781 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.32788} =?= DivisionSemiring ?m.33789 ▶
[Meta.isDefEq] ✅️ ?m.33786 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.32788} =?= Semifield ?m.33792 ▶
[Meta.isDefEq] ✅️ ?m.33790 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.32788} =?= DivisionSemiring ?m.33794 ▶
[Meta.isDefEq] ✅️ ?m.33786 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.33796 ▶
[Meta.isDefEq] ✅️ ?m.33781 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.32788} =?= CommSemiring ?m.33800 ▶
[Meta.isDefEq] ✅️ ?m.33797 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.32788} =?= CommSemiring ?m.33802 ▶
[Meta.isDefEq] ✅️ ?m.33797 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.33804 ▶
[Meta.isDefEq] ✅️ ?m.33781 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.32788} =?= NonAssocSemiring ?m.33806 ▶
[Meta.isDefEq] ✅️ ?m.33777 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.33808 ▶
[Meta.isDefEq] ✅️ ?m.33728 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.33813 ▶
[Meta.isDefEq] ✅️ ?m.33809 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.32788} =?= NonUnitalCommSemiring ?m.33817 ▶
[Meta.isDefEq] ✅️ ?m.33814 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.32788} =?= NonUnitalCommSemiring ?m.33819 ▶
[Meta.isDefEq] ✅️ ?m.33814 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.33821 ▶
[Meta.isDefEq] ✅️ ?m.33809 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.33823 ▶
[Meta.isDefEq] ✅️ ?m.33809 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul ?m.33825 ▶
[Meta.isDefEq] ✅️ ?m.33714 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass ?m.33830 ▶
[Meta.isDefEq] ✅️ ?m.33826 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass ?m.33832 ▶
[Meta.isDefEq] ✅️ ?m.33826 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass ?m.33836 ▶
[Meta.isDefEq] ✅️ ?m.33833 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass ?m.33838 ▶
[Meta.isDefEq] ✅️ ?m.33833 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.32788} =?= MonoidWithZero Ordinal.{?u.33844} ▶
[Meta.isDefEq] ✅️ ?m.33839 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.33839 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.33833 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.33826 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ ?m.33714 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.33298 =?= HMul Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788} ▶
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.32788} =?= MonoidWithZero Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33210 =?= instHMul ▶
Termination.lean:622:11
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33221 ▶
[Meta.isDefEq] ✅️ ?m.32790 =?= ?m.33222 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33222 ?m.33225 =?= HPow ?m.33230 ?m.33231 ?m.33230 ▶
[Meta.isDefEq] ✅️ ?m.33226 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33222 =?= Pow Ordinal.{?u.33247} Ordinal.{?u.33247} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33222 ?m.33400 =?= HPow ?m.33405 ?m.33406 ?m.33405 ▶
[Meta.isDefEq] ✅️ ?m.33401 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33222 =?= Pow Ordinal.{?u.33419} Ordinal.{?u.33419} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33222 ?m.33484 =?= HPow ?m.33489 ?m.33490 ?m.33489 ▶
[Meta.isDefEq] ✅️ ?m.33485 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33222 =?= Pow Ordinal.{?u.33500} Ordinal.{?u.33500} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33222 ?m.33556 =?= HPow ?m.33561 ?m.33562 ?m.33561 ▶
[Meta.isDefEq] ✅️ ?m.33557 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33222 =?= Pow Ordinal.{?u.33572} Ordinal.{?u.33572} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33222 ?m.33628 =?= HPow ?m.33633 ?m.33634 ?m.33633 ▶
[Meta.isDefEq] ✅️ ?m.33629 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33222 =?= Pow Ordinal.{?u.33644} Ordinal.{?u.33644} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33222 ?m.33851 =?= HPow ?m.33856 ?m.33857 ?m.33856 ▶
[Meta.isDefEq] ✅️ ?m.33852 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33222 =?= Pow Ordinal.{?u.33867} Ordinal.{?u.33867} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33222 ?m.33896 =?= HPow ?m.33901 ?m.33902 ?m.33901 ▶
[Meta.isDefEq] ✅️ ?m.33897 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33222 =?= Pow Ordinal.{?u.33912} Ordinal.{?u.33912} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.32788} ?m.33222 ?m.33938 =?= HPow ?m.33943 ?m.33944 ?m.33943 ▶
[Meta.isDefEq] ✅️ ?m.33939 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?m.33222 =?= Pow Ordinal.{?u.33954} Ordinal.{?u.33954} ▶
[Meta.isDefEq] ✅️ ?m.33224 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.32788} ?β =?= Pow Ordinal.{?u.33989} Ordinal.{?u.33989} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.32788} =?= Monoid Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:622:20
[Meta.isDefEq] 💥️ OfNat ?m.32790 2 =?= OfNat ℕ+ ?m.32799 ▶
[Meta.isDefEq] 💥️ OfNat ?m.32790 2 =?= OfNat ℕ+ ?m.32859 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33222 2 =?= OfNat ℕ+ ?m.33366 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33222 2 =?= OfNat ℕ+ ?m.33458 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33222 2 =?= OfNat ℕ+ ?m.33530 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33222 2 =?= OfNat ℕ+ ?m.33602 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33222 2 =?= OfNat ℕ+ ?m.33708 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33222 2 =?= OfNat ℕ+ ?m.33894 ▶
[Meta.isDefEq] 💥️ OfNat ?m.33222 2 =?= OfNat ℕ+ ?m.33936 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 2 =?= OfNat ℕ ?m.34000 ▶
[Meta.isDefEq] ✅️ ?m.33997 =?= instOfNatNat 2 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 2 =?= OfNat ℕ 2
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ?m.32792 =?= instOfNatNat 2 ▶
Termination.lean:622:25
[Meta.isDefEq] ✅️ Type ?u.33150 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type ?u.33151 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.33152) =?= Type (?u.32788 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788}
Ordinal.{?u.32788} =?= HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.32807 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33250 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33251 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.33254 =?= HAdd ?m.33257 ?m.33257 ?m.33257 ▶
[Meta.isDefEq] ✅️ ?m.33255 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.32788} =?= Add Ordinal.{?u.33268} ▶
[Meta.isDefEq] ✅️ ?m.33258 =?= add ▶
[Meta.isDefEq] ✅️ ?m.33258 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.33252 =?= HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788} ▶
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.32788} =?= Add Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33253 =?= instHAdd ▶
Termination.lean:622:29
[Meta.isDefEq] 💥️ OfNat ?m.32807 1 =?= OfNat ℕ+ ?m.32817 ▶
[Meta.isDefEq] 💥️ OfNat ?m.32807 1 =?= OfNat ℕ+ ?m.32868 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.32788} 1 =?= OfNat Ordinal.{?u.32788} 1
[Meta.isDefEq] ✅️ ?m.32809 =?= One.toOfNat1 ▶
Termination.lean:622:11
[Meta.isDefEq] ✅️ Type ?u.33147 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type ?u.33148 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.33149) =?= Type (?u.32788 + 1) ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.32788} Ordinal.{?u.32788}
Ordinal.{?u.32788} =?= HMul Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33223 =?= ?m.33272 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33273 ▶
[Meta.isDefEq] 💥️ HMul ?m.33272 Ordinal.{?u.32788} ?m.33276 =?= HMul ?m.33281 ?m.33281 ?m.33281 ▶
[Meta.isDefEq] 💥️ HMul ?m.33272 Ordinal.{?u.32788} ?m.33420 =?= HMul ?m.33425 ?m.33425 ?m.33425 ▶
[Meta.isDefEq] 💥️ HMul ?m.33272 Ordinal.{?u.32788} ?m.33501 =?= HMul ?m.33506 ?m.33506 ?m.33506 ▶
[Meta.isDefEq] 💥️ HMul ?m.33272 Ordinal.{?u.32788} ?m.33573 =?= HMul ?m.33578 ?m.33578 ?m.33578 ▶
[Meta.isDefEq] 💥️ HMul ?m.33272 Ordinal.{?u.32788} ?m.33645 =?= HMul ?m.33650 ?m.33650 ?m.33650 ▶
[Meta.isDefEq] 💥️ HMul ?m.33272 Ordinal.{?u.32788} ?m.33868 =?= HMul ?m.33873 ?m.33873 ?m.33873 ▶
[Meta.isDefEq] 💥️ HMul ?m.33272 Ordinal.{?u.32788} ?m.33913 =?= HMul ?m.33918 ?m.33918 ?m.33918 ▶
[Meta.isDefEq] 💥️ HMul ?m.33272 Ordinal.{?u.32788} ?m.33955 =?= HMul ?m.33960 ?m.33960 ?m.33960 ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.34001 =?= HMul ?m.34004 ?m.34004 ?m.34004 ▶
[Meta.isDefEq] ✅️ ?m.34002 =?= instHMul ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul ?m.34015 ▶
[Meta.isDefEq] ✅️ ?m.34005 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.32788} =?= Distrib ?m.34018 ▶
[Meta.isDefEq] ✅️ ?m.34016 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.34024 ▶
[Meta.isDefEq] ✅️ ?m.34019 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocCommSemiring ?m.34027 ▶
[Meta.isDefEq] ✅️ ?m.34025 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.32788} =?= NonUnitalNonAssocCommRing ?m.34030 ▶
[Meta.isDefEq] ✅️ ?m.34028 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.32788} =?= NonUnitalCommRing ?m.34033 ▶
[Meta.isDefEq] ✅️ ?m.34031 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.32788} =?= CommRing ?m.34036 ▶
[Meta.isDefEq] ✅️ ?m.34034 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.34038 ▶
[Meta.isDefEq] ✅️ ?m.34019 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.34043 ▶
[Meta.isDefEq] ✅️ ?m.34039 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.34045 ▶
[Meta.isDefEq] ✅️ ?m.34039 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.32788} =?= NonAssocRing ?m.34048 ▶
[Meta.isDefEq] ✅️ ?m.34046 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.32788} =?= Ring ?m.34052 ▶
[Meta.isDefEq] ✅️ ?m.34049 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.32788} =?= DivisionRing ?m.34055 ▶
[Meta.isDefEq] ✅️ ?m.34053 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.32788} =?= Ring ?m.34057 ▶
[Meta.isDefEq] ✅️ ?m.34049 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.32788} =?= NonUnitalNonAssocRing ?m.34059 ▶
[Meta.isDefEq] ✅️ ?m.34039 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.32788} =?= NonUnitalRing ?m.34063 ▶
[Meta.isDefEq] ✅️ ?m.34060 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.32788} =?= NonUnitalRing ?m.34065 ▶
[Meta.isDefEq] ✅️ ?m.34060 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.34067 ▶
[Meta.isDefEq] ✅️ ?m.34019 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.32788} =?= NonAssocSemiring ?m.34071 ▶
[Meta.isDefEq] ✅️ ?m.34068 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.34076 ▶
[Meta.isDefEq] ✅️ ?m.34072 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.32788} =?= DivisionSemiring ?m.34080 ▶
[Meta.isDefEq] ✅️ ?m.34077 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.32788} =?= Semifield ?m.34083 ▶
[Meta.isDefEq] ✅️ ?m.34081 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.32788} =?= DivisionSemiring ?m.34085 ▶
[Meta.isDefEq] ✅️ ?m.34077 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.34087 ▶
[Meta.isDefEq] ✅️ ?m.34072 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.32788} =?= CommSemiring ?m.34091 ▶
[Meta.isDefEq] ✅️ ?m.34088 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.32788} =?= CommSemiring ?m.34093 ▶
[Meta.isDefEq] ✅️ ?m.34088 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.32788} =?= Semiring ?m.34095 ▶
[Meta.isDefEq] ✅️ ?m.34072 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.32788} =?= NonAssocSemiring ?m.34097 ▶
[Meta.isDefEq] ✅️ ?m.34068 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.32788} =?= NonUnitalNonAssocSemiring ?m.34099 ▶
[Meta.isDefEq] ✅️ ?m.34019 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.34104 ▶
[Meta.isDefEq] ✅️ ?m.34100 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.32788} =?= NonUnitalCommSemiring ?m.34108 ▶
[Meta.isDefEq] ✅️ ?m.34105 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.32788} =?= NonUnitalCommSemiring ?m.34110 ▶
[Meta.isDefEq] ✅️ ?m.34105 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.34112 ▶
[Meta.isDefEq] ✅️ ?m.34100 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.32788} =?= NonUnitalSemiring ?m.34114 ▶
[Meta.isDefEq] ✅️ ?m.34100 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul ?m.34116 ▶
[Meta.isDefEq] ✅️ ?m.34005 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass ?m.34121 ▶
[Meta.isDefEq] ✅️ ?m.34117 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass ?m.34123 ▶
[Meta.isDefEq] ✅️ ?m.34117 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass ?m.34127 ▶
[Meta.isDefEq] ✅️ ?m.34124 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass ?m.34129 ▶
[Meta.isDefEq] ✅️ ?m.34124 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.32788} =?= MonoidWithZero Ordinal.{?u.34135} ▶
[Meta.isDefEq] ✅️ ?m.34130 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.34130 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.34124 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.34117 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ ?m.34005 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ HMul Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.33286 =?= HMul Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788} ▶
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.32788} =?= MonoidWithZero Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.32788} =?= MulZeroOneClass Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.32788} =?= MulZeroClass Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.32788} =?= Mul Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33275 =?= instHMul ▶
Termination.lean:622:11
[Meta.isDefEq] ✅️ Type ?u.33144 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type ?u.33145 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.33146) =?= Type (?u.32788 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788}
Ordinal.{?u.32788} =?= HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.32822 ▶
[Meta.isDefEq] ✅️ ?m.33274 =?= ?m.33286 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33287 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33286 Ordinal.{?u.32788} ?m.33290 =?= HAdd ?m.33293 ?m.33293 ?m.33293 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33286 Ordinal.{?u.32788} ?m.33430 =?= HAdd ?m.33433 ?m.33433 ?m.33433 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33286 Ordinal.{?u.32788} ?m.33508 =?= HAdd ?m.33511 ?m.33511 ?m.33511 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33286 Ordinal.{?u.32788} ?m.33580 =?= HAdd ?m.33583 ?m.33583 ?m.33583 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33286 Ordinal.{?u.32788} ?m.33652 =?= HAdd ?m.33655 ?m.33655 ?m.33655 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33286 Ordinal.{?u.32788} ?m.33875 =?= HAdd ?m.33878 ?m.33878 ?m.33878 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33286 Ordinal.{?u.32788} ?m.33920 =?= HAdd ?m.33923 ?m.33923 ?m.33923 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33286 Ordinal.{?u.32788} ?m.33962 =?= HAdd ?m.33965 ?m.33965 ?m.33965 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.34139 =?= HAdd ?m.34142 ?m.34142 ?m.34142 ▶
[Meta.isDefEq] ✅️ ?m.34140 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.32788} =?= Add Ordinal.{?u.34153} ▶
[Meta.isDefEq] ✅️ ?m.34143 =?= add ▶
[Meta.isDefEq] ✅️ ?m.34143 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.33299 =?= HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788} ▶
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.32788} =?= Add Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33289 =?= instHAdd ▶
Termination.lean:622:34
[Meta.isDefEq] 💥️ OfNat ?m.32822 1 =?= OfNat ℕ+ ?m.32832 ▶
[Meta.isDefEq] 💥️ OfNat ?m.32822 1 =?= OfNat ℕ+ ?m.32877 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.32788} 1 =?= OfNat Ordinal.{?u.32788} 1
[Meta.isDefEq] ✅️ ?m.32824 =?= One.toOfNat1 ▶
Termination.lean:620:6
[Meta.isDefEq] 💥️ Ordinal.{?u.32736} =?= Ordinal.{?u.32746}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.32746} x Ordinal.{?u.32736} =?= CoeT ?m.32886 ?m.32887 ?m.32886 ▶
[Meta.isDefEq] ✅️ ?m.32880 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.32746} x Ordinal.{?u.32736} =?= CoeT Ordinal.{?u.32746} x Ordinal.{?u.32746} ▶
[Meta.isDefEq] ✅️ Type (?u.32746 + 1) =?= Type (?u.32746 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.32746} =?= Ordinal.{?u.32746}
[Meta.isDefEq] ✅️ Ordinal.{?u.32746} =?= Ordinal.{?u.32746}
[Meta.isDefEq] 💥️ Ordinal.{?u.32746} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.32746} =?= CoeT ?m.32904 ?m.32905 ?m.32904 ▶
[Meta.isDefEq] ✅️ ?m.32898 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.17740} x Ordinal.{?u.32746} =?= CoeT Ordinal.{?u.17740} x Ordinal.{?u.17740} ▶
[Meta.isDefEq] ✅️ Type (?u.17740 + 1) =?= Type (?u.17740 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] ✅️ Ordinal.{?u.17740} =?= Ordinal.{?u.17740}
[Meta.isDefEq] 💥️ Ordinal.{?u.17740} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.32788} x Ordinal.{?u.17740} =?= CoeT ?m.32922 ?m.32923 ?m.32922 ▶
[Meta.isDefEq] ✅️ ?m.32916 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.32788} x Ordinal.{?u.17740} =?= CoeT Ordinal.{?u.32788} x Ordinal.{?u.32788} ▶
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Ordinal.{?u.32788} =?= ?m.33308 ▶
[Meta.isDefEq] ✅️ ?m.33300 =?= Ordinal.{?u.32788} ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.32788} =?= LE ?m.33313 ▶
[Meta.isDefEq] ✅️ ?m.33310 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.32788} =?= Preorder ?m.33317 ▶
[Meta.isDefEq] ✅️ ?m.33314 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.32788} =?= PartialOrder Ordinal.{?u.33329} ▶
[Meta.isDefEq] ✅️ ?m.33318 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.33318 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.33314 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.32788} =?= LE Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.32788} =?= PartialOrder Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.32788} =?= Preorder Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33309 =?= partialOrder.toLE ▶
Termination.lean:621:8
[Meta.isDefEq] ✅️ Type ?u.32933 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Type ?u.32934 =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.32935) =?= Type (?u.32788 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} ?m.32936 =?= HAdd ?m.32939 ?m.32939 ?m.32939 ▶
[Meta.isDefEq] ✅️ ?m.32937 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.32788} =?= Add Ordinal.{?u.32953} ▶
[Meta.isDefEq] ✅️ ?m.32940 =?= add ▶
[Meta.isDefEq] ✅️ ?m.32940 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788}
Ordinal.{?u.32788} =?= HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ Type (?u.32788 + 1) =?= Type (?u.32788 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.32788} =?= Add Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33209 =?= ?m.33298 ▶
[Meta.isDefEq] ✅️ ?m.33288 =?= ?m.33299 ▶
[Meta.isDefEq] 💥️ HAdd ?m.33298 ?m.33299 ?m.33302 =?= HAdd Std.Time.Week.Offset Std.Time.Week.Offset Std.Time.Week.Offset ▶
[Meta.isDefEq] 💥️ HAdd ?m.33298 ?m.33299 ?m.33438 =?= HAdd Std.Time.Week.Offset Std.Time.Week.Offset Std.Time.Week.Offset ▶
[Meta.isDefEq] 💥️ HAdd ?m.33298 ?m.33299 ?m.33513 =?= HAdd Std.Time.Week.Offset Std.Time.Week.Offset Std.Time.Week.Offset ▶
[Meta.isDefEq] 💥️ HAdd ?m.33298 ?m.33299 ?m.33585 =?= HAdd Std.Time.Week.Offset Std.Time.Week.Offset Std.Time.Week.Offset ▶
[Meta.isDefEq] 💥️ HAdd ?m.33298 ?m.33299 ?m.33657 =?= HAdd Std.Time.Week.Offset Std.Time.Week.Offset Std.Time.Week.Offset ▶
[Meta.isDefEq] 💥️ HAdd Ordinal.{?u.32788} ?m.33299 ?m.33880 =?= HAdd ?m.33883 ?m.33883 ?m.33883 ▶
[Meta.isDefEq] 💥️ HAdd Ordinal.{?u.32788} ?m.33299 ?m.33925 =?= HAdd ?m.33928 ?m.33928 ?m.33928 ▶
[Meta.isDefEq] 💥️ HAdd Ordinal.{?u.32788} ?m.33299 ?m.33967 =?= HAdd ?m.33970 ?m.33970 ?m.33970 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.32788} Ordinal.{?u.32788}
Ordinal.{?u.32788} =?= HAdd Ordinal.{?u.32788} Ordinal.{?u.32788} Ordinal.{?u.32788}
[Meta.isDefEq] ✅️ ?m.33301 =?= instHAdd ▶
Termination.lean:623:32
[Meta.isDefEq] ✅️ ?m.34169 ≤ ?m.34170 =?= mu a + 1 ≤ X + 1 ▶
[Meta.isDefEq] ✅️ mu a + 1 ≤ X + 1 =?= mu a + 1 ≤ X + 1 ▶
Termination.lean:623:36
[Meta.isDefEq] 💥️ Ordinal.{?u.32788} =?= Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.34202} x Ordinal.{?u.32788} =?= CoeT ?m.34232 ?m.34233 ?m.34232 ▶
[Meta.isDefEq] ✅️ ?m.34226 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.34202} x Ordinal.{?u.32788} =?= CoeT Ordinal.{?u.34202} x Ordinal.{?u.34202} ▶
[Meta.isDefEq] ✅️ Type (?u.34202 + 1) =?= Type (?u.34202 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.34202} =?= Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ Ordinal.{?u.34202} =?= Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ Ordinal.{?u.34202} =?= Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ Ordinal.{?u.34202} =?= ?m.34243 ▶
[Meta.isDefEq] ✅️ ?m.34204 =?= ?m.34244 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.34202} ?m.34244 ?m.34247 =?= HPow ?m.34252 ?m.34253 ?m.34252 ▶
[Meta.isDefEq] ✅️ ?m.34248 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.34202} ?m.34244 =?= Pow Ordinal.{?u.34269} Ordinal.{?u.34269} ▶
[Meta.isDefEq] ✅️ ?m.34245 =?= Ordinal.{?u.34202} ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.34202} =?= Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.34202} ?m.34244 ?m.34510 =?= HPow ?m.34515 ?m.34516 ?m.34515 ▶
[Meta.isDefEq] ✅️ ?m.34511 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.34202} ?m.34244 =?= Pow Ordinal.{?u.34529} Ordinal.{?u.34529} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.34202} ?m.34244 ?m.34538 =?= HPow ?m.34543 ?m.34544 ?m.34543 ▶
[Meta.isDefEq] ✅️ ?m.34539 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.34202} ?m.34244 =?= Pow Ordinal.{?u.34554} Ordinal.{?u.34554} ▶
[Meta.isDefEq] ✅️ ?m.34246 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.34202} ?β =?= Pow Ordinal.{?u.34572} Ordinal.{?u.34572} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.34202} =?= Monoid Ordinal.{?u.34586} ▶
[Meta.isDefEq] ✅️ ?m.34580 =?= monoid ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.34202} =?= Monoid Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:623:45
[Meta.isDefEq] 💥️ OfNat ?m.34204 3 =?= OfNat ℕ+ ?m.34213 ▶
[Meta.isDefEq] 💥️ OfNat ?m.34204 3 =?= OfNat ℕ+ ?m.34223 ▶
[Meta.isDefEq] 💥️ OfNat ?m.34244 3 =?= OfNat ℕ+ ?m.34506 ▶
[Meta.isDefEq] 💥️ OfNat ?m.34244 3 =?= OfNat ℕ+ ?m.34536 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ 3
[Meta.isDefEq] ✅️ ?m.34206 =?= instOfNatNat 3 ▶
Termination.lean:623:4
[Meta.isDefEq] ✅️ mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) =?= mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1)
[Meta.isDefEq] ✅️ mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) =?= mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ▶
Termination.lean:623:15
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.34202} =?= Mul ?m.34279 ▶
[Meta.isDefEq] ✅️ ?m.34272 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.34202} =?= Distrib ?m.34283 ▶
[Meta.isDefEq] ✅️ ?m.34280 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.34202} =?= NonUnitalNonAssocSemiring ?m.34291 ▶
[Meta.isDefEq] ✅️ ?m.34284 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.34202} =?= NonUnitalNonAssocCommSemiring ?m.34296 ▶
[Meta.isDefEq] ✅️ ?m.34292 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.34202} =?= NonUnitalNonAssocCommRing ?m.34301 ▶
[Meta.isDefEq] ✅️ ?m.34297 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.34202} =?= NonUnitalCommRing ?m.34306 ▶
[Meta.isDefEq] ✅️ ?m.34302 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.34202} =?= CommRing ?m.34311 ▶
[Meta.isDefEq] ✅️ ?m.34307 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.34202} =?= NonUnitalNonAssocSemiring ?m.34315 ▶
[Meta.isDefEq] ✅️ ?m.34284 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.34202} =?= NonUnitalNonAssocRing ?m.34320 ▶
[Meta.isDefEq] ✅️ ?m.34316 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.34202} =?= NonUnitalNonAssocRing ?m.34324 ▶
[Meta.isDefEq] ✅️ ?m.34316 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.34202} =?= NonAssocRing ?m.34327 ▶
[Meta.isDefEq] ✅️ ?m.34325 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.34202} =?= Ring ?m.34333 ▶
[Meta.isDefEq] ✅️ ?m.34328 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.34202} =?= DivisionRing ?m.34338 ▶
[Meta.isDefEq] ✅️ ?m.34334 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.34202} =?= Ring ?m.34342 ▶
[Meta.isDefEq] ✅️ ?m.34328 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.34202} =?= NonUnitalNonAssocRing ?m.34344 ▶
[Meta.isDefEq] ✅️ ?m.34316 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.34202} =?= NonUnitalRing ?m.34348 ▶
[Meta.isDefEq] ✅️ ?m.34345 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.34202} =?= NonUnitalRing ?m.34352 ▶
[Meta.isDefEq] ✅️ ?m.34345 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.34202} =?= NonUnitalNonAssocSemiring ?m.34354 ▶
[Meta.isDefEq] ✅️ ?m.34284 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.34202} =?= NonAssocSemiring ?m.34358 ▶
[Meta.isDefEq] ✅️ ?m.34355 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.34202} =?= Semiring ?m.34365 ▶
[Meta.isDefEq] ✅️ ?m.34359 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.34202} =?= DivisionSemiring ?m.34371 ▶
[Meta.isDefEq] ✅️ ?m.34366 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.34202} =?= Semifield ?m.34376 ▶
[Meta.isDefEq] ✅️ ?m.34372 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.34202} =?= DivisionSemiring ?m.34380 ▶
[Meta.isDefEq] ✅️ ?m.34366 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.34202} =?= Semiring ?m.34382 ▶
[Meta.isDefEq] ✅️ ?m.34359 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.34202} =?= CommSemiring ?m.34386 ▶
[Meta.isDefEq] ✅️ ?m.34383 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.34202} =?= CommSemiring ?m.34390 ▶
[Meta.isDefEq] ✅️ ?m.34383 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.34202} =?= Semiring ?m.34392 ▶
[Meta.isDefEq] ✅️ ?m.34359 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.34202} =?= NonAssocSemiring ?m.34394 ▶
[Meta.isDefEq] ✅️ ?m.34355 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.34202} =?= NonUnitalNonAssocSemiring ?m.34396 ▶
[Meta.isDefEq] ✅️ ?m.34284 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.34202} =?= NonUnitalSemiring ?m.34401 ▶
[Meta.isDefEq] ✅️ ?m.34397 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.34202} =?= NonUnitalCommSemiring ?m.34407 ▶
[Meta.isDefEq] ✅️ ?m.34402 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.34202} =?= NonUnitalCommSemiring ?m.34411 ▶
[Meta.isDefEq] ✅️ ?m.34402 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.34202} =?= NonUnitalSemiring ?m.34413 ▶
[Meta.isDefEq] ✅️ ?m.34397 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.34202} =?= NonUnitalSemiring ?m.34415 ▶
[Meta.isDefEq] ✅️ ?m.34397 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.34202} =?= Mul ?m.34417 ▶
[Meta.isDefEq] ✅️ ?m.34272 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.34202} =?= MulZeroClass ?m.34422 ▶
[Meta.isDefEq] ✅️ ?m.34418 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.34202} =?= MulZeroClass ?m.34426 ▶
[Meta.isDefEq] ✅️ ?m.34418 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.34202} =?= MulZeroOneClass ?m.34430 ▶
[Meta.isDefEq] ✅️ ?m.34427 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.34202} =?= MulZeroOneClass ?m.34434 ▶
[Meta.isDefEq] ✅️ ?m.34427 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.34202} =?= MonoidWithZero Ordinal.{?u.34440} ▶
[Meta.isDefEq] ✅️ ?m.34435 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.34435 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.34427 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.34418 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.34202} =?= Mul Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ Type (?u.34202 + 1) =?= Type (?u.34202 + 1)
[Meta.isDefEq] ✅️ Type (?u.34202 + 1) =?= Type (?u.34202 + 1)
[Meta.isDefEq] ✅️ Type (?u.34202 + 1) =?= Type (?u.34202 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.34202} =?= MonoidWithZero Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.34202} =?= MulZeroOneClass Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.34202} =?= MulZeroClass Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ ?m.34166 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.34202} =?= LE ?m.34447 ▶
[Meta.isDefEq] ✅️ ?m.34444 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.34202} =?= Preorder ?m.34451 ▶
[Meta.isDefEq] ✅️ ?m.34448 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.34202} =?= PartialOrder Ordinal.{?u.34463} ▶
[Meta.isDefEq] ✅️ ?m.34452 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.34452 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.34448 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.34202} =?= LE Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ Type (?u.34202 + 1) =?= Type (?u.34202 + 1)
[Meta.isDefEq] ✅️ Type (?u.34202 + 1) =?= Type (?u.34202 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.34202} =?= PartialOrder Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.34202} =?= Preorder Ordinal.{?u.34202}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34202} Ordinal.{?u.34202} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass Ordinal.{?u.34470} Ordinal.{?u.34470} (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.34466 =?= mulLeftMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34202} Ordinal.{?u.34202} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= MulLeftMono Ordinal.{?u.34202} ▶
[Meta.isDefEq] ✅️ ?m.34168 =?= mulLeftMono ▶
[Meta.isDefEq] ✅️ ?m.34163 =?= ω ^ 3 _ (mu a + 1) ≤ ω ^ 3 _ (X + 1) ▶
[Meta.isDefEq] ✅️ ω ^ 3 _ (mu a + 1) ≤ ω ^ 3 _ (X + 1) =?= ω ^ 3 _ (mu a + 1) ≤ ω ^ 3 _ (X + 1) ▶
Termination.lean:623:35
[Meta.isDefEq] ✅️ Ordinal.{?u.34202} =?= Ordinal.{?u.34202}
Termination.lean:624:32
[Meta.isDefEq] ✅️ ?m.34597 ≤ ?m.34598 =?= mu b + 1 ≤ X + 1 ▶
[Meta.isDefEq] ✅️ mu b + 1 ≤ X + 1 =?= mu b + 1 ≤ X + 1 ▶
Termination.lean:624:36
[Meta.isDefEq] 💥️ Ordinal.{?u.34202} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.34631} x Ordinal.{?u.34202} =?= CoeT ?m.34661 ?m.34662 ?m.34661 ▶
[Meta.isDefEq] ✅️ ?m.34655 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.34631} x Ordinal.{?u.34202} =?= CoeT Ordinal.{?u.34631} x Ordinal.{?u.34631} ▶
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= ?m.34672 ▶
[Meta.isDefEq] ✅️ ?m.34633 =?= ?m.34673 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.34631} ?m.34673 ?m.34676 =?= HPow ?m.34681 ?m.34682 ?m.34681 ▶
[Meta.isDefEq] ✅️ ?m.34677 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.34631} ?m.34673 =?= Pow Ordinal.{?u.34698} Ordinal.{?u.34698} ▶
[Meta.isDefEq] ✅️ ?m.34674 =?= Ordinal.{?u.34631} ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.34631} ?m.34673 ?m.34939 =?= HPow ?m.34944 ?m.34945 ?m.34944 ▶
[Meta.isDefEq] ✅️ ?m.34940 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.34631} ?m.34673 =?= Pow Ordinal.{?u.34958} Ordinal.{?u.34958} ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.34631} ?m.34673 ?m.34967 =?= HPow ?m.34972 ?m.34973 ?m.34972 ▶
[Meta.isDefEq] ✅️ ?m.34968 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.34631} ?m.34673 =?= Pow Ordinal.{?u.34983} Ordinal.{?u.34983} ▶
[Meta.isDefEq] ✅️ ?m.34675 =?= instHPow ▶
[Meta.isDefEq] 💥️ Pow Ordinal.{?u.34631} ?β =?= Pow Ordinal.{?u.35001} Ordinal.{?u.35001} ▶
[Meta.isDefEq] ✅️ ?inst✝ =?= Monoid.toNatPow ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.34631} =?= Monoid Ordinal.{?u.35015} ▶
[Meta.isDefEq] ✅️ ?m.35009 =?= monoid ▶
[Meta.isDefEq] ✅️ Monoid Ordinal.{?u.34631} =?= Monoid Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ ?inst✝ =?= monoid ▶
Termination.lean:624:45
[Meta.isDefEq] 💥️ OfNat ?m.34633 2 =?= OfNat ℕ+ ?m.34642 ▶
[Meta.isDefEq] 💥️ OfNat ?m.34633 2 =?= OfNat ℕ+ ?m.34652 ▶
[Meta.isDefEq] 💥️ OfNat ?m.34673 2 =?= OfNat ℕ+ ?m.34935 ▶
[Meta.isDefEq] 💥️ OfNat ?m.34673 2 =?= OfNat ℕ+ ?m.34965 ▶
[Meta.isDefEq] ✅️ OfNat ℕ 2 =?= OfNat ℕ 2
[Meta.isDefEq] ✅️ ?m.34635 =?= instOfNatNat 2 ▶
Termination.lean:624:4
[Meta.isDefEq] ✅️ mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) =?= mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1)
[Meta.isDefEq] ✅️ mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) =?= mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1)
Termination.lean:624:15
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.34631} =?= Mul ?m.34708 ▶
[Meta.isDefEq] ✅️ ?m.34701 =?= Distrib.toMul ▶
[Meta.isDefEq] ✅️ Distrib Ordinal.{?u.34631} =?= Distrib ?m.34712 ▶
[Meta.isDefEq] ✅️ ?m.34709 =?= NonUnitalNonAssocSemiring.toDistrib ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.34631} =?= NonUnitalNonAssocSemiring ?m.34720 ▶
[Meta.isDefEq] ✅️ ?m.34713 =?= NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommSemiring Ordinal.{?u.34631} =?= NonUnitalNonAssocCommSemiring ?m.34725 ▶
[Meta.isDefEq] ✅️ ?m.34721 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocCommRing Ordinal.{?u.34631} =?= NonUnitalNonAssocCommRing ?m.34730 ▶
[Meta.isDefEq] ✅️ ?m.34726 =?= NonUnitalCommRing.toNonUnitalNonAssocCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalCommRing Ordinal.{?u.34631} =?= NonUnitalCommRing ?m.34735 ▶
[Meta.isDefEq] ✅️ ?m.34731 =?= CommRing.toNonUnitalCommRing ▶
[Meta.isDefEq] ✅️ CommRing Ordinal.{?u.34631} =?= CommRing ?m.34740 ▶
[Meta.isDefEq] ✅️ ?m.34736 =?= Field.toCommRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.34631} =?= NonUnitalNonAssocSemiring ?m.34744 ▶
[Meta.isDefEq] ✅️ ?m.34713 =?= NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.34631} =?= NonUnitalNonAssocRing ?m.34749 ▶
[Meta.isDefEq] ✅️ ?m.34745 =?= NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.34631} =?= NonUnitalNonAssocRing ?m.34753 ▶
[Meta.isDefEq] ✅️ ?m.34745 =?= NonAssocRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonAssocRing Ordinal.{?u.34631} =?= NonAssocRing ?m.34756 ▶
[Meta.isDefEq] ✅️ ?m.34754 =?= Ring.toNonAssocRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.34631} =?= Ring ?m.34762 ▶
[Meta.isDefEq] ✅️ ?m.34757 =?= DivisionRing.toRing ▶
[Meta.isDefEq] ✅️ DivisionRing Ordinal.{?u.34631} =?= DivisionRing ?m.34767 ▶
[Meta.isDefEq] ✅️ ?m.34763 =?= Field.toDivisionRing ▶
[Meta.isDefEq] ✅️ Ring Ordinal.{?u.34631} =?= Ring ?m.34771 ▶
[Meta.isDefEq] ✅️ ?m.34757 =?= CommRing.toRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocRing Ordinal.{?u.34631} =?= NonUnitalNonAssocRing ?m.34773 ▶
[Meta.isDefEq] ✅️ ?m.34745 =?= NonUnitalRing.toNonUnitalNonAssocRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.34631} =?= NonUnitalRing ?m.34777 ▶
[Meta.isDefEq] ✅️ ?m.34774 =?= NonUnitalCommRing.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalRing Ordinal.{?u.34631} =?= NonUnitalRing ?m.34781 ▶
[Meta.isDefEq] ✅️ ?m.34774 =?= Ring.toNonUnitalRing ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.34631} =?= NonUnitalNonAssocSemiring ?m.34783 ▶
[Meta.isDefEq] ✅️ ?m.34713 =?= NonAssocSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.34631} =?= NonAssocSemiring ?m.34787 ▶
[Meta.isDefEq] ✅️ ?m.34784 =?= Semiring.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.34631} =?= Semiring ?m.34794 ▶
[Meta.isDefEq] ✅️ ?m.34788 =?= DivisionSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.34631} =?= DivisionSemiring ?m.34800 ▶
[Meta.isDefEq] ✅️ ?m.34795 =?= Semifield.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semifield Ordinal.{?u.34631} =?= Semifield ?m.34805 ▶
[Meta.isDefEq] ✅️ ?m.34801 =?= Field.toSemifield ▶
[Meta.isDefEq] ✅️ DivisionSemiring Ordinal.{?u.34631} =?= DivisionSemiring ?m.34809 ▶
[Meta.isDefEq] ✅️ ?m.34795 =?= DivisionRing.toDivisionSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.34631} =?= Semiring ?m.34811 ▶
[Meta.isDefEq] ✅️ ?m.34788 =?= CommSemiring.toSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.34631} =?= CommSemiring ?m.34815 ▶
[Meta.isDefEq] ✅️ ?m.34812 =?= Semifield.toCommSemiring ▶
[Meta.isDefEq] ✅️ CommSemiring Ordinal.{?u.34631} =?= CommSemiring ?m.34819 ▶
[Meta.isDefEq] ✅️ ?m.34812 =?= CommRing.toCommSemiring ▶
[Meta.isDefEq] ✅️ Semiring Ordinal.{?u.34631} =?= Semiring ?m.34821 ▶
[Meta.isDefEq] ✅️ ?m.34788 =?= Ring.toSemiring ▶
[Meta.isDefEq] ✅️ NonAssocSemiring Ordinal.{?u.34631} =?= NonAssocSemiring ?m.34823 ▶
[Meta.isDefEq] ✅️ ?m.34784 =?= NonAssocRing.toNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalNonAssocSemiring Ordinal.{?u.34631} =?= NonUnitalNonAssocSemiring ?m.34825 ▶
[Meta.isDefEq] ✅️ ?m.34713 =?= NonUnitalSemiring.toNonUnitalNonAssocSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.34631} =?= NonUnitalSemiring ?m.34830 ▶
[Meta.isDefEq] ✅️ ?m.34826 =?= NonUnitalCommSemiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.34631} =?= NonUnitalCommSemiring ?m.34836 ▶
[Meta.isDefEq] ✅️ ?m.34831 =?= NonUnitalCommRing.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalCommSemiring Ordinal.{?u.34631} =?= NonUnitalCommSemiring ?m.34840 ▶
[Meta.isDefEq] ✅️ ?m.34831 =?= CommSemiring.toNonUnitalCommSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.34631} =?= NonUnitalSemiring ?m.34842 ▶
[Meta.isDefEq] ✅️ ?m.34826 =?= Semiring.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ NonUnitalSemiring Ordinal.{?u.34631} =?= NonUnitalSemiring ?m.34844 ▶
[Meta.isDefEq] ✅️ ?m.34826 =?= NonUnitalRing.toNonUnitalSemiring ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.34631} =?= Mul ?m.34846 ▶
[Meta.isDefEq] ✅️ ?m.34701 =?= MulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.34631} =?= MulZeroClass ?m.34851 ▶
[Meta.isDefEq] ✅️ ?m.34847 =?= NonUnitalNonAssocSemiring.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.34631} =?= MulZeroClass ?m.34855 ▶
[Meta.isDefEq] ✅️ ?m.34847 =?= MulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.34631} =?= MulZeroOneClass ?m.34859 ▶
[Meta.isDefEq] ✅️ ?m.34856 =?= NonAssocSemiring.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.34631} =?= MulZeroOneClass ?m.34863 ▶
[Meta.isDefEq] ✅️ ?m.34856 =?= MonoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.34631} =?= MonoidWithZero Ordinal.{?u.34869} ▶
[Meta.isDefEq] ✅️ ?m.34864 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.34864 =?= monoidWithZero ▶
[Meta.isDefEq] ✅️ ?m.34856 =?= monoidWithZero.toMulZeroOneClass ▶
[Meta.isDefEq] ✅️ ?m.34847 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass ▶
[Meta.isDefEq] ✅️ Mul Ordinal.{?u.34631} =?= Mul Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{?u.34631} =?= MonoidWithZero Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{?u.34631} =?= MulZeroOneClass Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{?u.34631} =?= MulZeroClass Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ ?m.34594 =?= monoidWithZero.toMulZeroOneClass.toMulZeroClass.toMul ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.34631} =?= LE ?m.34876 ▶
[Meta.isDefEq] ✅️ ?m.34873 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.34631} =?= Preorder ?m.34880 ▶
[Meta.isDefEq] ✅️ ?m.34877 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.34631} =?= PartialOrder Ordinal.{?u.34892} ▶
[Meta.isDefEq] ✅️ ?m.34881 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.34881 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.34877 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.34631} =?= LE Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.34631} =?= PartialOrder Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.34631} =?= Preorder Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass Ordinal.{?u.34899} Ordinal.{?u.34899} (fun x1 x2 => x1 _ x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.34895 =?= mulLeftMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 =?= MulLeftMono Ordinal.{?u.34631} ▶
[Meta.isDefEq] ✅️ ?m.34596 =?= mulLeftMono ▶
[Meta.isDefEq] ✅️ ?m.34591 =?= ω ^ 2 _ (mu b + 1) ≤ ω ^ 2 _ (X + 1) ▶
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu b + 1) ≤ ω ^ 2 _ (X + 1) =?= ω ^ 2 _ (mu b + 1) ≤ ω ^ 2 _ (X + 1) ▶
Termination.lean:624:35
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
Termination.lean:625:11
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Type (u*1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace → Type (u_1 + 1) =?= Trace → Type (u_1 + 1)
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Zero Ordinal.{u_1} =?= Zero Ordinal.{u_1}
[Meta.isDefEq] ✅️ OfNat Ordinal.{u_1} 0 =?= OfNat Ordinal.{u_1} 0
[Meta.isDefEq] ✅️ Unit → Ordinal.{u_1} =?= Unit → Ordinal.{u_1}
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ outParam (Type (u_1 + 1)) =?= Type (u_1 + 1) ▶
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{u_1} =?= Add Ordinal.{u_1}
[Meta.isDefEq] ✅️ HAdd Ordinal.{u_1} Ordinal.{u_1} Ordinal.{u_1} =?= HAdd Ordinal.{u_1} Ordinal.{u_1} Ordinal.{u_1}
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ outParam (Type (u_1 + 1)) =?= Type (u_1 + 1) ▶
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ MonoidWithZero Ordinal.{u_1} =?= MonoidWithZero Ordinal.{u_1}
[Meta.isDefEq] ✅️ MulZeroOneClass Ordinal.{u_1} =?= MulZeroOneClass Ordinal.{u_1}
[Meta.isDefEq] ✅️ MulZeroClass Ordinal.{u_1} =?= MulZeroClass Ordinal.{u_1}
[Meta.isDefEq] ✅️ Mul Ordinal.{u_1} =?= Mul Ordinal.{u_1}
[Meta.isDefEq] ✅️ HMul Ordinal.{u_1} Ordinal.{u_1} Ordinal.{u_1} =?= HMul Ordinal.{u_1} Ordinal.{u_1} Ordinal.{u_1}
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ outParam (Type (u_1 + 1)) =?= Type (u_1 + 1) ▶
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ Pow Ordinal.{u_1} Ordinal.{u_1} =?= Pow Ordinal.{u_1} Ordinal.{u_1}
[Meta.isDefEq] ✅️ HPow Ordinal.{u_1} Ordinal.{u_1} Ordinal.{u_1} =?= HPow Ordinal.{u_1} Ordinal.{u_1} Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{u_1} =?= AddMonoidWithOne Ordinal.{u_1}
[Meta.isDefEq] ✅️ NatCast Ordinal.{u_1} =?= NatCast Ordinal.{u_1}
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 5 =?= (3 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{u_1} 5 =?= OfNat Ordinal.{u_1} 5
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (u_1 + 1) =?= Type (u_1 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{u_1} =?= One Ordinal.{u_1}
[Meta.isDefEq] ✅️ OfNat Ordinal.{u_1} 1 =?= OfNat Ordinal.{u_1} 1
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace → Ordinal.{u_1} =?= Trace → Ordinal.{u_1}
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ NatCast Ordinal.{u_1} =?= NatCast Ordinal.{u_1}
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 4 =?= (2 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{u_1} 4 =?= OfNat Ordinal.{u_1} 4
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace → Ordinal.{u_1} =?= Trace → Ordinal.{u_1}
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ NatCast Ordinal.{u_1} =?= NatCast Ordinal.{u_1}
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 3 =?= (1 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{u_1} 3 =?= OfNat Ordinal.{u_1} 3
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ NatCast Ordinal.{u_1} =?= NatCast Ordinal.{u_1}
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 2 =?= (0 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{u_1} 2 =?= OfNat Ordinal.{u_1} 2
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace → Trace → Ordinal.{u_1} =?= Trace → Trace → Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ NatCast Ordinal.{u_1} =?= NatCast Ordinal.{u_1}
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 6 =?= (4 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{u_1} 6 =?= OfNat Ordinal.{u_1} 6
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace → Trace → Trace → Ordinal.{u_1} =?= Trace → Trace → Trace → Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ NatCast Ordinal.{u_1} =?= NatCast Ordinal.{u_1}
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 9 =?= (7 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{u_1} 9 =?= OfNat Ordinal.{u_1} 9
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace → Trace → Ordinal.{u_1} =?= Trace → Trace → Ordinal.{u_1}
[Meta.isDefEq] ✅️ Ordinal.{u_1} =?= Ordinal.{u_1}
[Meta.isDefEq] ✅️ Trace → Prop =?= Trace → Prop
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ x✝ = x →
mu x✝ =
match x✝ with
| void => 0
| t.delta => ω ^ 5 * (mu t + 1) + 1
| t.integrate => ω ^ 4 _ (mu t + 1) + 1
| a.merge b => ω ^ 3 _ (mu a + 1) + ω ^ 2 _ (mu b + 1) + 1
| b.recΔ s n => ω ^ (mu n + 6) _ (ω ^ 3 _ (mu s + 1) + 1) + ω _ (mu b + 1) + 1
| a.eqW b => ω ^ (mu a + mu b + 9) + 1 =?= x✝ = x →
mu x✝ =
match x✝ with
| void => 0
| t.delta => ω ^ 5 _ (mu t + 1) + 1
| t.integrate => ω ^ 4 _ (mu t + 1) + 1
| a.merge b => ω ^ 3 _ (mu a + 1) + ω ^ 2 _ (mu b + 1) + 1
| b.recΔ s n => ω ^ (mu n + 6) _ (ω ^ 3 _ (mu s + 1) + 1) + ω _ (mu b + 1) + 1
| a.eqW b => ω ^ (mu a + mu b + 9) + 1
Termination.lean:625:19
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?a =?= ?b ▶
[Meta.isDefEq] ✅️ ?b =?= ?b
Termination.lean:625:29
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?a =?= ?b ▶
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?b =?= ?b
[Meta.isDefEq] ✅️ ?c =?= ?c
Termination.lean:625:44
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
Termination.lean:626:23
[Meta.isDefEq] ✅️ ?m.39289 ≤ ?m.39290 =?= ω ^ 3 _ (mu a + 1) ≤ ω ^ 3 _ (X + 1) ▶
[Meta.isDefEq] ✅️ ω ^ 3 _ (mu a + 1) ≤ ω ^ 3 _ (X + 1) =?= ω ^ 3 _ (mu a + 1) ≤ ω ^ 3 _ (X + 1) ▶
Termination.lean:626:38
[Meta.isDefEq] ✅️ ?m.39413 ≤ ?m.39414 =?= ω ^ 2 _ (mu b + 1) ≤ ω ^ 2 _ (X + 1) ▶
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu b + 1) ≤ ω ^ 2 _ (X + 1) =?= ω ^ 2 _ (mu b + 1) ≤ ω ^ 2 _ (X + 1) ▶
Termination.lean:626:27
[Meta.isDefEq] 💥️ Add ?m.39408 =?= Add ((i : ?m.39447) → ?m.39448 i) ▶
[Meta.isDefEq] 💥️ Preorder ?m.39408 =?= Preorder ((i : ?m.39480) → ?m.39481 i) ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.39408 ?m.39408 (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass ℕ+ ℕ+ (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] 💥️ CovariantClass ?m.39408 ?m.39408 (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass (WithTop ?m.39519) (WithTop ?m.39519) (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.39291 ≤ ?m.39292 =?= ?m.39413 + ?m.39415 ≤ ?m.39414 + ?m.39416 ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.34631} =?= Add Ordinal.{?u.39621} ▶
[Meta.isDefEq] ✅️ ?m.39614 =?= add ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.34631} =?= Add Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ ?m.39409 =?= add ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.34631} =?= Preorder Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= CovariantClass Ordinal.{?u.39626} Ordinal.{?u.39626} (fun x1 x2 => x1 + x2) fun x1 x2 => x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.39623 =?= instAddLeftMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddLeftMono Ordinal.{?u.34631} ▶
[Meta.isDefEq] ✅️ ?m.39411 =?= instAddLeftMono ▶
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.39668} Ordinal.{?u.39668} (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.39667} Ordinal.{?u.39667} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.39661 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.34631} ▶
[Meta.isDefEq] ✅️ ?m.39412 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu b + 1) + ?m.39565 ≤
ω ^ 2 _ (X + 1) + ?m.39565 =?= ω ^ 2 _ (mu b + 1) + ?m.39565 ≤ ω ^ 2 _ (X + 1) + ?m.39565 ▶
Termination.lean:626:41
[Meta.isDefEq] 💥️ Preorder ?m.39563 =?= Preorder ((i : ?m.39595) → ?m.39596 i) ▶
[Meta.isDefEq] ✅️ ?m.39415 ≤ ?m.39416 =?= ?m.39565 ≤ ?m.39565 ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.34631} =?= Preorder ?m.39601 ▶
[Meta.isDefEq] ✅️ ?m.39599 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.34631} =?= PartialOrder Ordinal.{?u.39612} ▶
[Meta.isDefEq] ✅️ ?m.39602 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.39602 =?= partialOrder ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.34631} =?= Preorder Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.34631} =?= PartialOrder Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ✅️ ?m.39565 ≤ ?m.39565 =?= ?m.39565 ≤ ?m.39565 ▶
Termination.lean:625:4
type mismatch, term
add*le_add t1 (add_le_add t2 le_rfl)
after simplification has type
HPow.hPow.{?u.34631 + 1, 0, ?u.34631 + 1} ω 3 * Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) : Prop
but is expected to have type
HPow.hPow.{?u.34631 + 1, ?u.34631 + 1, ?u.34631 + 1} ω 3 _ Order.succ (mu a) +
Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) : Prop
Termination.lean:625:4
[Meta.Tactic.simp.rewrite] unfold mu, mu (a.merge b) ==> ω ^ 3 _ (mu a + 1) + ω ^ 2 _ (mu b + 1) + 1
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu a + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu a + 1
==>
Order.succ (mu a)
[Meta.isDefEq] ❌️ ?a + ?b =?= mu b + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu b + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu b + 1
==>
Order.succ (mu b)
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ (mu a) + ω ^ 2 _ Order.succ (mu b) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ (mu a) + ω ^ 2 _ Order.succ (mu b) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ (mu a) + ω ^ 2 _ Order.succ (mu b) + 1 ▶
[Meta.isDefEq] ✅️ ?a + ?b + ?c =?= ω ^ 3 _ Order.succ (mu a) + ω ^ 2 _ Order.succ (mu b) + 1 ▶
[Meta.Tactic.simp.rewrite] add_assoc:1000:
ω ^ 3 _ Order.succ (mu a) + ω ^ 2 _ Order.succ (mu b) + 1
==>
ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + 1)
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 2 _ Order.succ (mu b) + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= ω ^ 2 _ Order.succ (mu b) + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
ω ^ 2 _ Order.succ (mu b) + 1
==>
Order.succ (ω ^ 2 _ Order.succ (mu b))
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ▶
[Meta.isDefEq] ✅️ X =?= X
[Meta.Tactic.simp.rewrite] hX:1000:
X
==>
mu a + mu b
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + mu b ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + mu b + 1 ▶
[Meta.isDefEq] ✅️ ?a + ?b + ?c =?= mu a + mu b + 1 ▶
[Meta.Tactic.simp.rewrite] add_assoc:1000:
mu a + mu b + 1
==>
mu a + (mu b + 1)
[Meta.isDefEq] ❌️ ?a + ?b =?= mu b + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu b + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu b + 1
==>
Order.succ (mu b)
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + Order.succ (mu b) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + Order.succ (mu b) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 2 _ (mu a + Order.succ (mu b)) + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= ω ^ 2 _ (mu a + Order.succ (mu b)) + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
ω ^ 2 _ (mu a + Order.succ (mu b)) + 1
==>
Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b)))
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ✅️ ?x ≥
?y =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ✅️ ?a ≤
?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ Subsingleton Ordinal.{?u.34631} =?= Subsingleton ?m.37564 ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.34631} =?= Subsingleton ?m.37566 ▶
[Meta.isDefEq] ✅️ ?m.37561 =?= Unique.instSubsingleton ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.34631} =?= Subsingleton ?m.37568 ▶
[Meta.isDefEq] ✅️ ?m.37561 =?= IsEmpty.instSubsingleton ▶
[Meta.isDefEq] ❌️ ?a ≤
?a +
?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?b +
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a +
?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?b +
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?a +
?c =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?b + ?a ≤
?c +
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ✅️ ?x ≥
?y =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ✅️ ?a ≤
?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a +
?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?b +
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a +
?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a ≤
?b +
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?b =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?a +
?c =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ❌️ ?b + ?a ≤
?c +
?a =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ✅️ ?x ≥
?y =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.Tactic.simp.rewrite] ge_iff_le:1000:
ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b)))
==>
ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b)))
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu a + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu a + 1
==>
Order.succ (mu a)
[Meta.isDefEq] ❌️ ?a + ?b =?= mu b + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu b + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu b + 1
==>
Order.succ (mu b)
[Meta.isDefEq] ❌️ fun as => Array.filterMap some as =?= ?m.39565 ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 2 _ Order.succ (mu b) + ?m.39565 ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 2 _ Order.succ (mu b) + ?m.39565 ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + (?b + ?c) =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + (?b + ?c) =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ▶
[Meta.isDefEq] ✅️ X =?= X
[Meta.Tactic.simp.rewrite] hX:1000:
X
==>
mu a + mu b
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + mu b ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + mu b + 1 ▶
[Meta.isDefEq] ✅️ ?a + ?b + ?c =?= mu a + mu b + 1 ▶
[Meta.Tactic.simp.rewrite] add_assoc:1000:
mu a + mu b + 1
==>
mu a + (mu b + 1)
[Meta.isDefEq] ❌️ ?a + ?b =?= mu b + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= mu b + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
mu b + 1
==>
Order.succ (mu b)
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + Order.succ (mu b) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= mu a + Order.succ (mu b) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565 ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565 ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + (?b + ?c) =?= ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + (?b + ?c) =?= ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ✅️ ?x ≥
?y =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ✅️ ?a ≤
?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a +
?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?b +
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a +
?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?b +
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?a +
?c =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?b + ?a ≤
?c +
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ✅️ ?x ≥
?y =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ✅️ ?a ≤
?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a +
?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?b +
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?a +
?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a ≤
?b +
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?b =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤
?a +
?c =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ?b + ?a ≤
?c +
?a =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) +
Order.succ
(ω ^ 2 _
(mu a +
Order.succ
(mu
b))) =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) +
Order.succ
(ω ^ 2 _
(mu a +
Order.succ
(mu
b))) =?= ω ^ 3 _ Order.succ (mu a) + (ω ^ 2 _ Order.succ (mu b) + ?m.39565) ≤
ω ^ 3 _ (mu a + Order.succ (mu b)) + (ω ^ 2 _ (mu a + Order.succ (mu b)) + ?m.39565) ▶
[Meta.isDefEq] ✅️ @LE.le =?= @LE.le
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ (mu a) +
(ω ^ 2 _ Order.succ (mu b) + ?m.39565) =?= ω ^ 3 _ Order.succ (mu a) + Order.succ (ω ^ 2 _ Order.succ (mu b)) ▶
[Meta.isDefEq] ✅️ ω ^ 3 _ (mu a + Order.succ (mu b)) +
(ω ^ 2 _ (mu a + Order.succ (mu b)) +
?m.39565) =?= ω ^ 3 _ (mu a + Order.succ (mu b)) + Order.succ (ω ^ 2 _ (mu a + Order.succ (mu b))) ▶
[Meta.isDefEq] ✅️ @HAdd.hAdd =?= @HAdd.hAdd
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ instHAdd =?= instHAdd ▶
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ (mu a) =?= ω ^ 3 _ Order.succ (mu a) ▶
[Meta.isDefEq] ❌️ ω ^ 2 _ Order.succ (mu b) + 1 =?= Order.succ (ω ^ 2 _ Order.succ (mu b)) ▶
[Meta.isDefEq] ✅️ @HMul.hMul =?= @HMul.hMul
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ instHMul =?= instHMul
[Meta.isDefEq] ❌️ ω ^ 3 =?= ω ^ 3 ▶
[Meta.isDefEq] ✅️ Order.succ (mu a) =?= Order.succ (mu a)
[Meta.isDefEq] ❌️ @HPow.hPow =?= @HPow.hPow ▶
Termination.lean:626:12
[Meta.isDefEq] ✅️ Add Ordinal.{?u.34631} =?= Add Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ ?m.39285 =?= add ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.34631} =?= Preorder Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddLeftMono Ordinal.{?u.34631} ▶
[Meta.isDefEq] ✅️ ?m.39287 =?= instAddLeftMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.34631} Ordinal.{?u.34631} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.34631} ▶
[Meta.isDefEq] ✅️ ?m.39288 =?= instAddRightMono ▶
Termination.lean:626:26
[Meta.isDefEq] ✅️ ω ^ 2 _ (mu b + 1) + ?m.39565 ≤
ω ^ 2 _ (X + 1) + ?m.39565 =?= ω ^ 2 _ (mu b + 1) + ?m.39565 ≤ ω ^ 2 _ (X + 1) + ?m.39565 ▶
Termination.lean:627:2
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
Termination.lean:627:18
[Meta.isDefEq] ✅️ ?m.114712 =?= ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ✅️ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ≤ ω ^ (X + 5) =?= ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ≤ ω ^ (X + 5) ▶
Termination.lean:627:38
[Meta.isDefEq] ✅️ Ordinal.{?u.114713} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
Termination.lean:629:17
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:629:10
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:629:19
[Meta.isDefEq] ✅️ Trace =?= Trace
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:629:9
[Meta.isDefEq] ✅️ Trace =?= Trace
Termination.lean:629:6
[Meta.isDefEq] ✅️ Type ?u.114898 =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Type ?u.114899 =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.114900) =?= Type (?u.114757 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.114757} Ordinal.{?u.114757} ?m.114901 =?= HAdd ?m.114904 ?m.114904 ?m.114904 ▶
[Meta.isDefEq] ✅️ ?m.114902 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.114757} =?= Add Ordinal.{?u.114918} ▶
[Meta.isDefEq] ✅️ ?m.114905 =?= add ▶
[Meta.isDefEq] ✅️ ?m.114905 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.114757} Ordinal.{?u.114757}
Ordinal.{?u.114757} =?= HAdd Ordinal.{?u.114757} Ordinal.{?u.114757} Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.114757} =?= Add Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= ?m.114731 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= ?m.114921 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= ?m.114922 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.114757} Ordinal.{?u.114757} ?m.114925 =?= HAdd ?m.114928 ?m.114928 ?m.114928 ▶
[Meta.isDefEq] ✅️ ?m.114926 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.114757} =?= Add Ordinal.{?u.114939} ▶
[Meta.isDefEq] ✅️ ?m.114929 =?= add ▶
[Meta.isDefEq] ✅️ ?m.114929 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.114757} Ordinal.{?u.114757}
?m.114923 =?= HAdd Ordinal.{?u.114757} Ordinal.{?u.114757} Ordinal.{?u.114757} ▶
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.114757} =?= Add Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ ?m.114924 =?= instHAdd ▶
Termination.lean:629:24
[Meta.isDefEq] 💥️ OfNat ?m.114731 1 =?= OfNat ℕ+ ?m.114741 ▶
[Meta.isDefEq] 💥️ OfNat ?m.114731 1 =?= OfNat ℕ+ ?m.114752 ▶
[Meta.isDefEq] 💥️ OfNat ?m.114731 1 =?= OfNat ℕ+ ?m.114782 ▶
[Meta.isDefEq] 💥️ OfNat ?m.114731 1 =?= OfNat ℕ+ ?m.114846 ▶
[Meta.isDefEq] 💥️ OfNat ?m.114731 1 =?= OfNat ℕ+ ?m.114878 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.114757} 1 =?= OfNat ?m.115006 1 ▶
[Meta.isDefEq] ✅️ ?m.115002 =?= One.toOfNat1 ▶
[Meta.isDefEq] ✅️ One Ordinal.{?u.114757} =?= One Ordinal.{?u.115014} ▶
[Meta.isDefEq] ✅️ ?m.115007 =?= one ▶
[Meta.isDefEq] ✅️ ?m.115007 =?= one ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.114757} 1 =?= OfNat Ordinal.{?u.114757} 1
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ One Ordinal.{?u.114757} =?= One Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ ?m.114733 =?= One.toOfNat1 ▶
Termination.lean:629:38
[Meta.isDefEq] ✅️ Type ?u.114792 =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ Type ?u.114793 =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ outParam (Type ?u.114794) =?= Type (?u.34631 + 1) ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.34631} Ordinal.{?u.34631} ?m.114795 =?= HAdd ?m.114798 ?m.114798 ?m.114798 ▶
[Meta.isDefEq] ✅️ ?m.114796 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.34631} =?= Add Ordinal.{?u.114812} ▶
[Meta.isDefEq] ✅️ ?m.114799 =?= add ▶
[Meta.isDefEq] ✅️ ?m.114799 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.34631} Ordinal.{?u.34631}
Ordinal.{?u.34631} =?= HAdd Ordinal.{?u.34631} Ordinal.{?u.34631} Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.34631} =?= Add Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= ?m.114762 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= ?m.114814 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= ?m.114815 ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.34631} Ordinal.{?u.34631} ?m.114818 =?= HAdd ?m.114821 ?m.114821 ?m.114821 ▶
[Meta.isDefEq] ✅️ ?m.114819 =?= instHAdd ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.34631} =?= Add Ordinal.{?u.114832} ▶
[Meta.isDefEq] ✅️ ?m.114822 =?= add ▶
[Meta.isDefEq] ✅️ ?m.114822 =?= add ▶
[Meta.isDefEq] ✅️ HAdd Ordinal.{?u.34631} Ordinal.{?u.34631}
?m.114816 =?= HAdd Ordinal.{?u.34631} Ordinal.{?u.34631} Ordinal.{?u.34631} ▶
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ Add Ordinal.{?u.34631} =?= Add Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ ?m.114817 =?= instHAdd ▶
Termination.lean:629:42
[Meta.isDefEq] 💥️ OfNat ?m.114762 5 =?= OfNat ℕ+ ?m.114771 ▶
[Meta.isDefEq] 💥️ OfNat ?m.114762 5 =?= OfNat ℕ+ ?m.114790 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.34631} 5 =?= OfNat ?m.114851 ?m.114852 ▶
[Meta.isDefEq] ✅️ ?m.114848 =?= instOfNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.34631} =?= NatCast ?m.114858 ▶
[Meta.isDefEq] ✅️ ?m.114853 =?= AddMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.34631} =?= AddMonoidWithOne Ordinal.{?u.114864} ▶
[Meta.isDefEq] ✅️ ?m.114859 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.114859 =?= addMonoidWithOne ▶
[Meta.isDefEq] ✅️ ?m.114853 =?= addMonoidWithOne.toNatCast ▶
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 5 =?= (?m.114865 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.114854 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.114854 =?= instNatAtLeastTwo ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.34631} 5 =?= OfNat Ordinal.{?u.34631} 5
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Type (?u.34631 + 1) =?= Type (?u.34631 + 1)
[Meta.isDefEq] ✅️ AddMonoidWithOne Ordinal.{?u.34631} =?= AddMonoidWithOne Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ NatCast Ordinal.{?u.34631} =?= NatCast Ordinal.{?u.34631}
[Meta.isDefEq] ✅️ Type =?= Type
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ OfNat ℕ 3 =?= OfNat ℕ 3
[Meta.isDefEq] ✅️ ℕ =?= ℕ
[Meta.isDefEq] ✅️ Nat.AtLeastTwo 5 =?= (3 + 2).AtLeastTwo ▶
[Meta.isDefEq] ✅️ ?m.114764 =?= instOfNatAtLeastTwo ▶
Termination.lean:629:6
[Meta.isDefEq] 💥️ Ordinal.{?u.114729} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.114757} x Ordinal.{?u.114729} =?= CoeT ?m.114887 ?m.114888 ?m.114887 ▶
[Meta.isDefEq] ✅️ ?m.114881 =?= instCoeT ▶
[Meta.isDefEq] ✅️ CoeT Ordinal.{?u.114757} x Ordinal.{?u.114729} =?= CoeT Ordinal.{?u.114757} x Ordinal.{?u.114757} ▶
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= ?m.114977 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ LE Ordinal.{?u.114757} =?= LE ?m.114982 ▶
[Meta.isDefEq] ✅️ ?m.114979 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.114757} =?= Preorder ?m.114986 ▶
[Meta.isDefEq] ✅️ ?m.114983 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.114757} =?= PartialOrder Ordinal.{?u.114998} ▶
[Meta.isDefEq] ✅️ ?m.114987 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.114987 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.114983 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.114757} =?= LE Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.114757} =?= PartialOrder Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.114757} =?= Preorder Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ ?m.114978 =?= partialOrder.toLE ▶
Termination.lean:629:28
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= ?m.114946 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.34631} =?= ?m.114947 ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.114757} Ordinal.{?u.34631} ?m.114950 =?= HPow ?m.114954 ?m.114955 ?m.114954 ▶
[Meta.isDefEq] ✅️ ?m.114951 =?= instHPow ▶
[Meta.isDefEq] ✅️ Pow Ordinal.{?u.114757} Ordinal.{?u.34631} =?= Pow Ordinal.{?u.114964} Ordinal.{?u.114964} ▶
[Meta.isDefEq] ✅️ ?m.114956 =?= instPow ▶
[Meta.isDefEq] ✅️ ?m.114956 =?= instPow ▶
[Meta.isDefEq] ✅️ HPow Ordinal.{?u.114757} Ordinal.{?u.34631}
?m.114948 =?= HPow Ordinal.{?u.114757} Ordinal.{?u.114757} Ordinal.{?u.114757} ▶
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Pow Ordinal.{?u.114757} Ordinal.{?u.114757} =?= Pow Ordinal.{?u.114757} Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ ?m.114949 =?= instHPow ▶
Termination.lean:630:22
[Meta.isDefEq] ✅️ ?m.115054 ≤ ?m.115055 =?= mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ▶
[Meta.isDefEq] ✅️ mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) =?= mu (a.merge b) ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ▶
Termination.lean:630:5
[Meta.isDefEq] ✅️ Add Ordinal.{?u.114757} =?= Add Ordinal.{?u.115114} ▶
[Meta.isDefEq] ✅️ ?m.115107 =?= add ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.114757} =?= Add Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ ?m.115051 =?= add ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.114757} =?= LE Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.114757} Ordinal.{?u.114757} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.115123} Ordinal.{?u.115123} (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.114757} Ordinal.{?u.114757} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.115122} Ordinal.{?u.115122} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.115116 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.114757} Ordinal.{?u.114757} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.114757} ▶
[Meta.isDefEq] ✅️ ?m.115053 =?= instAddRightMono ▶
Termination.lean:630:34
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= ?m.115091 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.114757} 0 =?= OfNat ?m.115097 0 ▶
[Meta.isDefEq] ✅️ ?m.115093 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.114757} =?= Zero Ordinal.{?u.115104} ▶
[Meta.isDefEq] ✅️ ?m.115098 =?= zero ▶
[Meta.isDefEq] ✅️ ?m.115098 =?= zero ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.114757} 0 =?= OfNat Ordinal.{?u.114757} 0
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.114757} =?= Zero Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ ?m.115092 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
Termination.lean:632:15
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?a =?= ?b ▶
[Meta.isDefEq] ✅️ ?b =?= ?b
Termination.lean:632:25
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?a =?= ?b ▶
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
[Meta.isDefEq] ✅️ ?b =?= ?b
[Meta.isDefEq] ✅️ ?c =?= ?c
Termination.lean:632:40
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?G =?= ?G
[Meta.isDefEq] ✅️ ?inst✝ =?= ?inst✝
Termination.lean:633:33
[Meta.isDefEq] ✅️ ?m.127748 ≤ ?m.127749 =?= ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ✅️ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ≤ ω ^ (X + 5) =?= ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) ≤ ω ^ (X + 5) ▶
Termination.lean:632:8
type mismatch, term
add*le_add_right payload 0
after simplification has type
HPow.hPow.{?u.114757 + 1, ?u.114757 + 1, ?u.114757 + 1} ω 3 * Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤
ω ^ (X + 5) : Prop
but is expected to have type
HPow.hPow.{?u.114757 + 1, 0, ?u.114757 + 1} ω 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 : Prop
Termination.lean:632:8
[Meta.isDefEq] ❌️ ?a + ?b =?= X + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= X + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
X + 1
==>
Order.succ X
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 2 _ Order.succ X + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= ω ^ 2 _ Order.succ X + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
ω ^ 2 _ Order.succ X + 1
==>
Order.succ (ω ^ 2 _ Order.succ X)
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) + 0 ▶
[Meta.isDefEq] ✅️ ?a + 0 =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) + 0 ▶
[Meta.Tactic.simp.rewrite] add_zero:1000:
ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) + 0
==>
ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X)
[Meta.isDefEq] ❌️ fun as => Array.filterMap some as =?= ?m.115215 ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ Subsingleton Ordinal.{?u.114757} =?= Subsingleton ?m.127236 ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.114757} =?= Subsingleton ?m.127238 ▶
[Meta.isDefEq] ✅️ ?m.127233 =?= Unique.instSubsingleton ▶
[Meta.isDefEq] ✅️ Subsingleton Ordinal.{?u.114757} =?= Subsingleton ?m.127240 ▶
[Meta.isDefEq] ✅️ ?m.127233 =?= IsEmpty.instSubsingleton ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤ ?a =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤ ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤ ?a =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤ ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= X + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= X + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
X + 1
==>
Order.succ X
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 2 _ Order.succ X + 1 ▶
[Meta.isDefEq] ✅️ ?o + 1 =?= ω ^ 2 _ Order.succ X + 1 ▶
[Meta.Tactic.simp.rewrite] add_one_eq_succ:1000:
ω ^ 2 _ Order.succ X + 1
==>
Order.succ (ω ^ 2 _ Order.succ X)
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) + 0 ▶
[Meta.isDefEq] ✅️ ?a + 0 =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) + 0 ▶
[Meta.Tactic.simp.rewrite] add_zero:1000:
ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) + 0
==>
ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X)
[Meta.isDefEq] ❌️ ?a + ?b =?= X + 5 ▶
[Meta.isDefEq] ❌️ ?a + ?b =?= ω ^ (X + 5) + 0 ▶
[Meta.isDefEq] ✅️ ?a + 0 =?= ω ^ (X + 5) + 0 ▶
[Meta.Tactic.simp.rewrite] add_zero:1000:
ω ^ (X + 5) + 0
==>
ω ^ (X + 5)
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤ ?a =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤ ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ✅️ ?x ≥ ?y =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ ?a ≤ ?a =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ✅️ ?a ≤ ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤ ?a =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ ?a + ?b ≤ ?b =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤
?m.115215 =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤
?m.115215 =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ✅️ @LE.le =?= @LE.le
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) =?= ω ^ 3 _ Order.succ X + Order.succ (ω ^ 2 _ Order.succ X) ▶
[Meta.isDefEq] ✅️ ω ^ (X + 5) =?= ?m.115215 ▶
[Meta.isDefEq] ✅️ @HAdd.hAdd =?= @HAdd.hAdd
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ instHAdd =?= instHAdd
[Meta.isDefEq] ❌️ ω ^ 3 _ Order.succ X =?= ω ^ 3 _ Order.succ X ▶
[Meta.isDefEq] ❌️ Order.succ (ω ^ 2 _ Order.succ X) =?= Order.succ (ω ^ 2 _ Order.succ X) ▶
[Meta.isDefEq] ✅️ @HMul.hMul =?= @HMul.hMul
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ instHMul =?= instHMul
[Meta.isDefEq] ❌️ ω ^ 3 =?= ω ^ 3 ▶
[Meta.isDefEq] ✅️ Order.succ X =?= Order.succ X
[Meta.isDefEq] ❌️ @HPow.hPow =?= @HPow.hPow ▶
Termination.lean:633:16
[Meta.isDefEq] ✅️ Add Ordinal.{?u.114757} =?= Add Ordinal.{?u.127788} ▶
[Meta.isDefEq] ✅️ ?m.127781 =?= add ▶
[Meta.isDefEq] ✅️ Add Ordinal.{?u.114757} =?= Add Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ ?m.127745 =?= add ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.114757} =?= LE ?m.127793 ▶
[Meta.isDefEq] ✅️ ?m.127790 =?= Preorder.toLE ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.114757} =?= Preorder ?m.127797 ▶
[Meta.isDefEq] ✅️ ?m.127794 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.114757} =?= PartialOrder Ordinal.{?u.127809} ▶
[Meta.isDefEq] ✅️ ?m.127798 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.127798 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.127794 =?= partialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ LE Ordinal.{?u.114757} =?= LE Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.114757} =?= PartialOrder Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.114757} =?= Preorder Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ❌️ CovariantClass Ordinal.{?u.114757} Ordinal.{?u.114757} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.127818} Ordinal.{?u.127818} (Function.swap fun x1 x2 => x1 _ x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.114757} Ordinal.{?u.114757} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤
x2 =?= CovariantClass Ordinal.{?u.127817} Ordinal.{?u.127817} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 ▶
[Meta.isDefEq] ✅️ ?m.127811 =?= instAddRightMono ▶
[Meta.isDefEq] ✅️ CovariantClass Ordinal.{?u.114757} Ordinal.{?u.114757} (Function.swap fun x1 x2 => x1 + x2) fun x1 x2 =>
x1 ≤ x2 =?= AddRightMono Ordinal.{?u.114757} ▶
[Meta.isDefEq] ✅️ ?m.127747 =?= instAddRightMono ▶
Termination.lean:633:41
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= ?m.127761 ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.114757} 0 =?= OfNat ?m.127767 0 ▶
[Meta.isDefEq] ✅️ ?m.127763 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.114757} =?= Zero Ordinal.{?u.127776} ▶
[Meta.isDefEq] ✅️ ?m.127768 =?= zero ▶
[Meta.isDefEq] ✅️ ?m.127768 =?= zero ▶
[Meta.isDefEq] ✅️ OfNat Ordinal.{?u.114757} 0 =?= OfNat Ordinal.{?u.114757} 0
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ Zero Ordinal.{?u.114757} =?= Zero Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ ?m.127762 =?= Zero.toOfNat0 ▶
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
Termination.lean:628:2
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
Termination.lean:630:4
[Meta.isDefEq] ✅️ mu (a.merge b) + 0 ≤ ω ^ 3 _ (X + 1) + (ω ^ 2 _ (X + 1) + 1) + 0 =?= ?m.115213 ≤ ?m.115214 ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.114757} =?= Preorder ?m.115259 ▶
[Meta.isDefEq] ✅️ ?m.115257 =?= PartialOrder.toPreorder ▶
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.114757} =?= PartialOrder Ordinal.{?u.115269} ▶
[Meta.isDefEq] ✅️ ?m.115260 =?= partialOrder ▶
[Meta.isDefEq] ✅️ ?m.115260 =?= partialOrder ▶
[Meta.isDefEq] ✅️ Preorder Ordinal.{?u.114757} =?= Preorder Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Type (?u.114757 + 1) =?= Type (?u.114757 + 1)
[Meta.isDefEq] ✅️ PartialOrder Ordinal.{?u.114757} =?= PartialOrder Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ partialOrder.toPreorder =?= partialOrder.toPreorder
[Meta.isDefEq] ❌️ mu (a.merge b) + 1 ≤ ω ^ (X + 5) =?= mu (a.merge b) + 0 ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 1 ≤ ω ^ (X + 5) =?= mu (a.merge b) + 0 ≤ ?m.115215 ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ ?m.115215 =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] 💥️ CoeT (mu (a.merge b) + 0 ≤ ?m.115215) ⋯ (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeT ?m.120225 ?m.120226 ?m.120225 ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ ?m.115215 =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] 💥️ CoeT (mu (a.merge b) + 0 ≤ ?m.115215) ⋯ (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeT ?m.122222 ?m.122223 ?m.122222 ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ ?m.115215 =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] 💥️ CoeT (mu (a.merge b) + 0 ≤ ?m.115215) ⋯ (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeT ?m.124189 ?m.124190 ?m.124189 ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ ?m.115215 =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] 💥️ CoeT (mu (a.merge b) + 0 ≤ ?m.115215) ⋯ (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeT ?m.126156 ?m.126157 ?m.126156 ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ sorry =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] ❌️ CoeT (mu (a.merge b) + 0 ≤ sorry) ⋯ (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeT ?m.148699 ?m.148700 ?m.148699 ▶
[Meta.isDefEq] ✅️ CoeT (mu (a.merge b) + 0 ≤ sorry) ⋯ (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeT ?m.148794 ?m.148795 ?m.148796 ▶
[Meta.isDefEq] ✅️ ?m.148693 =?= instCoeTOfCoeDep ▶
[Meta.isDefEq] ✅️ CoeT (mu (a.merge b) + 0 ≤ sorry) ⋯ (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeT ?m.148798 ?m.148800 ?m.148799 ▶
[Meta.isDefEq] ✅️ ?m.148693 =?= instCoeTOfCoeHTCT ▶
[Meta.isDefEq] ❌️ CoeHTCT (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeHTCT ?m.148808 ?m.148808 ▶
[Meta.isDefEq] ✅️ CoeHTCT (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeHTCT ?m.148840 ?m.148841 ▶
[Meta.isDefEq] ✅️ ?m.148801 =?= instCoeHTCTOfCoeHTC ▶
[Meta.isDefEq] ❌️ CoeHTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeHTC ?m.148851 ?m.148851 ▶
[Meta.isDefEq] ✅️ CoeHTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeHTC ?m.148883 ?m.148884 ▶
[Meta.isDefEq] ✅️ ?m.148842 =?= instCoeHTCOfCoeOTC ▶
[Meta.isDefEq] ❌️ CoeOTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeOTC ?m.148894 ?m.148894 ▶
[Meta.isDefEq] ✅️ CoeOTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeOTC ?m.148926 ?m.148927 ▶
[Meta.isDefEq] ✅️ ?m.148885 =?= instCoeOTCOfCoeTC ▶
[Meta.isDefEq] ❌️ CoeTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeTC ?m.148937 ?m.148937 ▶
[Meta.isDefEq] ✅️ CoeTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeTC ?m.148969 ?m.148970 ▶
[Meta.isDefEq] ✅️ ?m.148928 =?= instCoeTCOfCoe*1 ▶
[Meta.isDefEq] ✅️ CoeTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeTC ?m.148976 ?m.148975 ▶
[Meta.isDefEq] ✅️ ?m.148928 =?= instCoeTCOfCoe ▶
[Meta.isDefEq] ✅️ CoeOTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeOTC ?m.148979 ?m.148981 ▶
[Meta.isDefEq] ✅️ ?m.148885 =?= instCoeOTCOfCoeOut ▶
[Meta.isDefEq] ✅️ CoeOut (mu (a.merge b) + 0 ≤ sorry) ?m.148980 =?= CoeOut ?m.148988 ?m.148989 ▶
[Meta.isDefEq] ✅️ ?m.148982 =?= instCoeOutOfCoeSort ▶
[Meta.isDefEq] ❌️ CoeSort (mu (a.merge b) + 0 ≤ sorry) ?m.148989 =?= CoeSort ?m.148997 (Type ?u.148996) ▶
[Meta.isDefEq] ✅️ CoeOut (mu (a.merge b) + 0 ≤ sorry) ?m.148980 =?= CoeOut ?m.149002 ?m.149003 ▶
[Meta.isDefEq] ✅️ ?m.148982 =?= instCoeOutOfCoeFun ▶
[Meta.isDefEq] ✅️ CoeFun (mu (a.merge b) + 0 ≤ sorry) fun x => ?m.149003 =?= CoeFun ?m.149010 fun x => (a : ?m.149011) → ?m.149012 a ▶
[Meta.isDefEq] ✅️ ?m.149004 =?= DFunLike.hasCoeToFun ▶
[Meta.isDefEq] ✅️ DFunLike (mu (a.merge b) + 0 ≤ sorry) ?m.149011 ?m.149012 =?= DFunLike ?m.149027 ?m.149028 fun x => ?m.149029 ▶
[Meta.isDefEq] ✅️ ?m.149013 =?= EquivLike.toFunLike ▶
[Meta.isDefEq] ✅️ CoeHTC (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeHTC ?m.149038 ?m.149040 ▶
[Meta.isDefEq] ✅️ ?m.148842 =?= instCoeHTCOfCoeHeadOfCoeOTC ▶
[Meta.isDefEq] ✅️ CoeHTCT (mu (a.merge b) + 0 ≤ sorry) (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeHTCT ?m.149045 ?m.149044 ▶
[Meta.isDefEq] ✅️ ?m.148801 =?= instCoeHTCTOfCoeTailOfCoeHTC ▶
[Meta.isDefEq] ❌️ CoeTail ?m.149043 (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeTail ℕ ?m.149052 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.149043 (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeTail ℤ ?m.149056 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.149043 (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeTail ℚ≥0 ?m.149058 ▶
[Meta.isDefEq] ❌️ CoeTail ?m.149043 (mu (a.merge b) + 1 ≤ ω ^ (X + 5)) =?= CoeTail ℚ ?m.149060 ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ sorry =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ sorry =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ sorry =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 ≤ sorry =?= mu (a.merge b) + 1 ≤ ω ^ (X + 5) ▶
[Meta.isDefEq] ❌️ LE.le (mu (a.merge b) + 0) =?= LE.le (mu (a.merge b) + 1) ▶
[Meta.isDefEq] ✅️ @LE.le =?= @LE.le
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ partialOrder.toLE =?= partialOrder.toLE
[Meta.isDefEq] ❌️ mu (a.merge b) + 0 =?= mu (a.merge b) + 1 ▶
[Meta.isDefEq] ❌️ sorry =?= ω ^ (X + 5) ▶
[Meta.isDefEq] ✅️ @HAdd.hAdd =?= @HAdd.hAdd
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ✅️ instHAdd =?= instHAdd
[Meta.isDefEq] ✅️ mu (a.merge b) =?= mu (a.merge b)
[Meta.isDefEq] ❌️ 0 =?= 1 ▶
[Meta.isDefEq] ✅️ @OfNat.ofNat =?= @OfNat.ofNat
[Meta.isDefEq] ✅️ Ordinal.{?u.114757} =?= Ordinal.{?u.114757}
[Meta.isDefEq] ❌️ 0 =?= 1
[Meta.isDefEq] ❌️ Zero.toOfNat0 =?= One.toOfNat1 ▶
Termination.lean:631:6
[Meta.isDefEq] ✅️ ω ^ 3 * (X + 1) + (ω ^ 2 _ (X + 1) + 1) + 0 ≤ ?m.115215 =?= ω ^ 3 _ (X + 1) + (ω ^ 2 \_ (X + 1) + 1) + 0 ≤ ?m.115215
Termination.lean:609:0
[diag] Diagnostics ▼
[reduction] unfolded declarations (max: 6412, num: 19): ▶
[reduction] unfolded instances (max: 4372, num: 19): ▶
[reduction] unfolded reducible declarations (max: 8878, num: 6): ▶
[def_eq] heuristic for solving f a =?= f b (max: 706, num: 3): ▶
use set_option diagnostics.threshold <num> to control threshold for reporting counters
Termination.lean:610:52
[Meta.isDefEq] ✅️ mu (a.merge b).integrate < mu (a.eqW b) =?= mu (a.merge b).integrate < mu (a.eqW b)
ChatGPT said:
Got the updated Ordinal Toolkit Combined Review document. I’ll base any future edits or guidance on this latest version—just let me know what you’d like to tackle next!

No file chosenNo file chosen
ChatGPT can make mistakes. OpenAI doesn't use Moussa Rahnama's Workspace workspace data to train its models.