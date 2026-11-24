import YM.FVAAlt2.WickPull

/-! Work inside the even part of the **native** super-vertex algebra.
Elements are the MS kernels with exactly the Symm/polynomial/Pure premises
needed for native operations. `forget` is injective and proves PowerSeries
multiplication and exponential here are exactly MS's ones.
Avoids mixing `(*)` here with (incorrect) pointwise product of kernel arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open MS MS.Koszul MS.Native MS.Plane MS.Book MS.Cylinder MS.Puff MS.Puff.Actors
open MS.Swirl MS.Puff.Mom MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open Filter Topology Function Finset
open scoped PowerSeries
set_option linter.unusedSectionVars false
variable {A J:Type}
def FlatEven (p:Sector A) := (Puff.Center p ⊓ FeeP p)
abbrev Com (p:Sector A) := ↥(FlatEven p)
variable {p:Sector A}

namespace Com
lemma even (x:Com p): Pure p false x.val:= (show _∧_ from x.property).1
lemma fee (x:Com p): x.val∈ FeeP p:= (show _∧_ from x.property).2
lemma sym (x:Com p): Symm p x.val:= (fee_spec (fee x)).1
lemma small (x:Com p): x.val ∈ Mini A:= (fee_spec (fee x)).2
lemma mem {X:Raw A ℂ}(hp: Pure p false X)(hf:X∈ FeeP p): X∈FlatEven p:=⟨hp,hf⟩

def piece (c:ℂ): Com p:= ⟨coin c, mem (coin_pure _) ⟨coin_symm c,minH (coinN _)⟩⟩

instance : One (Com p):=⟨piece 1⟩
instance : Mul (Com p):= ⟨fun x y=> ⟨product p x.val y.val,mem ((even x).prod (even y)) (fee_pair (fee x) (fee y))⟩⟩
@[simp] lemma piece_val (c:ℂ): (piece c : Com p).val=coin c:= rfl
@[simp] lemma one_val: (1:Com p).val=coin 1:= rfl
@[simp] lemma mul_val(x y:Com p): (x*y).val=product p x.val y.val:= rfl

instance : CommRing (Com p) where
  __ :=  (inferInstance : AddCommGroup (Com p))
  mul_one x:=Subtype.ext ((actor p).identityR _)
  one_mul x:=Subtype.ext ((actor p).identityK _)
  zero_mul x:=Subtype.ext (by change product p 0 x.val=0;simp)
  mul_zero x:=Subtype.ext (map_zero (product p x.val))
  left_distrib x y z:=Subtype.ext (map_add _ y.val z.val)
  right_distrib x y z:=Subtype.ext (add_times p ..)
  mul_comm x y:=Subtype.ext ((even x).central _)
  mul_assoc x y z:=Subtype.ext (times_assoc ..)
  natCast n:= n • (1:Com p)
  intCast n:= n • (1:Com p)
  natCast_zero:= zero_smul ..
  natCast_succ n:= by rw [add_smul,one_smul]
  intCast_ofNat n:= by change (n:ℤ) • (1:Com p)=n • (1:Com p); simp
  intCast_negSucc n:= by change Int.negSucc n • (1:Com p)= -((n+1) • (1:Com p)); simp
instance : Algebra ℂ (Com p) := Algebra.ofModule
  (fun _ (_ y:Com p)=>Subtype.ext (LinearMap.congr_fun (map_smul (product p) _ _) y.val))
  (fun _ (x _:Com p)=> Subtype.ext (map_smul (product p x.val) ..))

@[simp] lemma piece_mul (c:ℂ)(x:Com p): piece c*x=c • x:= Subtype.ext (coin_product ..)
@[simp] lemma alg_piece (c:ℂ): algebraMap ℂ (Com p) c=piece c:= by rw [Algebra.algebraMap_eq_smul_one,← piece_mul,mul_one]

/-- restriction hom to other bases -/
def transform [Fintype A][Fintype J]{q:Sector J} {L:Matrix J A ℂ}(H:Tie p q L): Com p→ₐ[ℂ] Com q where
  toFun x:= ⟨pull L x.val,mem (pull_pure H (even x)) (pull_fee H (fee x))⟩
  map_one':=Subtype.ext (pull_coin L 1)
  map_mul' _ _:=Subtype.ext (pull_product H ..)
  map_zero':=Subtype.ext (map_zero (pull L))
  map_add' _ _:=Subtype.ext (map_add (pull L) ..)
  commutes' c:= by rw [alg_piece,alg_piece]; exact Subtype.ext (pull_coin L c)

def forget (p:Sector A) : PowerSeries (Com p) →ₗ[ℂ] SpecB A := {
  toFun f i:= (PowerSeries.coeff i f).val
  map_add' _ _:=by funext i; rw [map_add]; rfl
  map_smul' _ _:=by funext i; rw [PowerSeries.coeff_smul]; rfl }

lemma forget_inj : Injective (forget p):=fun _ _ h=> PowerSeries.ext fun i=>Subtype.ext (congrFun h i)
@[simp] lemma forget_at (x:PowerSeries (Com p))(i:ℕ): forget p x i=(PowerSeries.coeff i x).val:=rfl
lemma forgets [Fintype A](x:PowerSeries (Com p)): Γ (forget p x) p := fun _ _=> fee _
lemma kept (x:PowerSeries (Com p)): forget p x∈ (PermV p).guard:= fun _ _=> even _ -- keyword
lemma forget_mul(f g:PowerSeries (Com p)): forget p (f*g) = (PermV p).core (forget p f) (forget p g):= by
  funext i; rw [forget_at,PowerSeries.coeff_mul,Submodule.coe_sum]; rfl
lemma forget_one: forget p (1:PowerSeries (Com p))=(PermV p).unit:= by
  funext i; rw [forget_at,PowerSeries.coeff_one]; change (if _ then _ else _ : Com p).val=(useN).refineV (coin 1) i; unfold SplitP.refineV; by_cases h:i=0 <;> simp [h,useN,SplitP.nat]
lemma forgetC (f:Com p): forget p (PowerSeries.C f)=useN.refineV f.val :=by funext i; rw [forget_at,PowerSeries.coeff_C]; unfold SplitP.refineV; by_cases h:i=0 <;> simp [h,useN,SplitP.nat]
lemma packed_series (F:SpecB A) (he:∀ i, Pure p false (F i))(hf:Γ F p): ∃ x:PowerSeries (Com p), F= forget p x := ⟨PowerSeries.mk (fun i=> ⟨F i,mem (he i) (hf i (Set.mem_univ _))⟩),funext fun i=> by rw [forget_at, PowerSeries.coeff_mk]⟩
end Com
end YM.FVAAlt2
