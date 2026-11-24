import YM.WilsonCoeffUV.Product.I.Rank
/-!
# Programmatic UV charges in evaluated-source price books
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open scoped Topology BigOperators
variable {N M m k e r d u i j b:ℕ}{H C D x δ:ℝ}{E W U:Credit}{G:Gauge}

def LowerD (G:Gauge)(k e r u:ℕ) := (lowerCost G k e r u).choose
def LowerF (I: Gear G)(k e r u:ℕ) := ((lowerCost G k e r u).choose_spec I).choose
def RoughD (G:Gauge)(k e r u:ℕ) := (roughCost G k e r u).choose
def RoughF (I:Gear G)(k e r u:ℕ) := ((roughCost G k e r u).choose_spec I).choose
-- Stand Gear integrated into roster
structure DormP (I:Gear G)(k e u:ℕ)(c:ℝ): Prop where
   pin r: 0<r → r≤ k+e → pinCost u I r≤ Real.exp (-Real.log I.patch.L.val/2)
   lo i r: i≤e → r≤k+e → LowerF I k i r u≤c
   hi i r: i≤e → r≤k+e → RoughF I k i r u≤c

def Dormitory (L:Realm G (e+1) E) (k u:ℕ)(P:Credit): Prop := ∀ m,∀ h:L.anchor≤m,DormP (L.mint m h).gear k e u (L.cash P m)
variable (L:Realm G (e+1) E)
def costXV (G:Gauge)(e:ℕ)(E:Credit) := Realm.jump E (full_vacuum G (e+1) E).choose
abbrev δWarm (m b:ℕ):= L.cash (doubling E) m*L.tempC m b
def ReelTime (v:i≤e)(ha:L.anchor≤m)(p:m<b)(q:b≤N)(h:b≤M): Rally (i+1) 0 (L.mint m ha).gear:= (L.mint m ha).readPast L.hG L.green (L.cash (costXV G e E) m) (δWarm L m b) (Credit.purchase _ (L.depth _ ha)) p q h (L.dominates_both ha p).1 (L.dominates_both ha p).2 (elderT L ha p q h fun i' j p'=> (full_vacuum G (e+1) E).choose_spec i' (by unfold lowerGrade at p'; omega) j)
lemma ReelTime.versN (k:ℕ)(v:i≤e)(ha:L.anchor≤m)(p:m<b)(q:b≤N)(h:b≤M)(P: Era G ℝ) : (verseI L.draws L.paid m N k P).2=sunI _ (ReelTime L v ha p q h).P k P.2:=rfl
lemma ReelTime.versM (k:ℕ)(v:i≤e)(ha:L.anchor≤m)(p:m<b)(q:b≤N)(h:b≤M)(P:Era G ℝ): (verseI L.draws L.paid m M k P).2=sunI _ (ReelTime L v ha p q h).Q k P.2:=rfl

def ticketL (G:Gauge)(e k i r u:ℕ)(E W: Credit): Credit:= W.prodC ((costXV G e E).powC (LowerD G k i r u))
def ticketU (G:Gauge)(e k i r u:ℕ)(E W:Credit): Credit:= W.prodC ((costXV G e E).powC (RoughD G k i r u))
abbrev thinLevel {G:Gauge}(A:Levels G)(m:ℕ)(x:ℝ):= x/(A.S.block m).val
def lowRep (S:Schedule)(m r:ℕ):ℝ:= if r=0 then 1 else Real.exp (-PathCost.arc S m/2)
lemma amen (t: Dormitory L k u W)(ha:L.anchor≤m)(p:m<N)(q:i≤e)(h:r≤k+e)(Y: Era G ℝ)(hY:Auth k Y)(v:0≤x)(hv:x≤1)(hA:Fruit 0 (thinLevel L.draws m x) u (Y.2 i r) C)(hw:0≤D) (f:∀ b l,lowerGrade b l i r→ Fruit 0 (thinLevel L.draws m x) u (Y.2 b l) D):
   Fruit 0 x u ((verseI L.draws L.paid m N k Y).2 i r) (lowRep L.draws.S m r*C + L.cash (ticketL G e k i r u E W) m * D):=by
    let I:= (L.mint m ha).gear; let V:= ReelTime L q ha p (le_refl N) (le_refl N); let X:= Y.2; let Q:DriftR I i r u:=⟨V,X,X,x,v,hv,D,hw,fun i j p=> YieldP.same (f i j p) V.θ⟩; rw [ReelTime.versN L k q ha p (le_refl N) (le_refl N)]; apply (((lowerCost G k i r u).choose_spec I).choose_spec.2 Q hY.roots hY.coverP C hA).more; have ht:0≤Q.seed.x:= zero_le_one.trans Q.seed.rich; rw [cash,ticketL, Credit.products,Credit.power]
    refine add_le_add (mul_le_mul_of_nonneg_right ?_ hA.C) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((t m ha).lo i r q h) (pow_nonneg ht (LowerD G k i r u))) hw)
    by_cases hh:r=0; · rw [pinCost,if_pos hh,lowRep,if_pos hh]
    unfold lowRep; rw [if_neg hh, arch]; exact (t m ha).pin r (Nat.pos_of_ne_zero hh) h
lemma urgent (t: Dormitory L k u W)(ha:L.anchor≤m)(p:m<b)(q:b≤N)(h:b≤M)(v:i≤e)(w:r≤k+e)(Y Z: Era G ℝ)(he:0≤x)(hv:x≤1)(hC:0≤C)(hy:∀ j l,j ≤ i → YieldP 0 (thinLevel L.draws m x) u C (δWarm L m b) (Y.2 j l) (Z.2 j l)): YieldP 0 x u (L.cash (ticketU G e k i r u E W) m*C) (δWarm L m b) ((verseI L.draws L.paid m N k Y).2 i r) ((verseI L.draws L.paid m M k Z).2 i r):=by
    let I:= (L.mint m ha).gear; let P:= ReelTime L v ha p q h; have ht:0≤P.x:=zero_le_one.trans P.rich
    rw [ReelTime.versN L k v ha p q h,ReelTime.versM L k v ha p q h]; apply (((roughCost G k i r u).choose_spec I).choose_spec.2 P Y.2 Z.2 x C he hv hC hy).step _ P.θ; rw [cash,ticketU,Credit.products,Credit.power]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((t m ha).hi _ _ v w) (pow_nonneg ht (RoughD G k i r u))) hC
end YM.WilsonCoeffUV.Mer
