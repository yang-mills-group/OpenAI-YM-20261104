import YM.MS.Theater.Pave
/-!
# Splitting at radial gauge.Fast volume.Unit matters.Drop weight1
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset MeasureTheory Real Maxwell
open Analysis Tensor Koszul Plane Landau Detect Local.BV InnerProductSpace Submodule
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h i r n:ℕ} {X: Feet G h}
abbrev Rad (G:Gauge)(i:ℕ):= LinearMap.ker ( radialX G i )
lemma in_rad (X:Feet G h): X∈ Rad G h↔ ∀ i:E4, ∑ a:Axis, i a • diagonal (X.val a) i=0:= by
    simp_rw [ ← tBudget ]; constructor; · intro hp; have hv : radialX G h X=0:= LinearMap.mem_ker.mp hp; rw [hv]; exact fun _=>rfl
    intro h; apply LinearMap.mem_ker.mpr; apply absolute; exact fun _=>h
-- n=0. radius determines.X even Unit directions.
lemma weightT (G:Gauge): Rad G 0=⊥:= by
    apply eq_bot_iff.mpr; intro x hx; apply (Submodule.mem_bot _).mpr; apply absolute; intro i p; have he:= ( in_rad x ).mp hx ( basis i ); rw [ show diagonal (x.val i) p= diagonal ( x.val i ) ( basis i ) from congr_arg (x.val i) (Subsingleton.elim ..) ]; simpa [ite_smul] using he
variable (G) in
def step_in (i:ℕ): Labels.Taylor G i →ₗ[ℝ] Feet G (i+1) where
    toFun X:= ⟨ X.val, X.property.1 ⟩
    map_add' X Y:= rfl
    map_smul' c X:=rfl
lemma seatR (X:Labels.Taylor G i): step_in G i X∈ Rad G (i+1):= (in_rad _).mpr X.property.2
variable (G) in
def offShell (h:ℕ): Labels.Taylor G h≃ₗ[ℝ]Rad G (h+1) where
    toFun X:=⟨step_in G h X,seatR X⟩
    invFun X:=⟨ X.val.val, X.val.property, (in_rad _).mp X.property ⟩
    left_inv X:= rfl
    right_inv X:=rfl
    map_add' _ _:=rfl
    map_smul' _ _:=rfl
-- projection
local notation "R'"=> radialX G h
local notation "L" => gradS G h
abbrev divYear (n:ℕ):ℝ:= n+1
lemma positive (n:ℕ): 0 < divYear n := by unfold divYear; positivity
def carve (G:Gauge)(h:ℕ): Module.End ℝ ( Feet G h ) := LinearMap.id- ( divYear h )⁻¹ • ( (gradS G h).comp ( radialX G h ) )
lemma carveΩ (X:Feet G h): carve G h X=X-( ( divYear h )⁻¹ ) • L ( R' X ):= rfl
lemma house (X:Feet G h): carve G h X∈ Rad G h:= by apply LinearMap.mem_ker.mpr; rw [ carveΩ, map_sub, map_smul,depart,inv_smul_smul₀ (positive h|>.ne'),sub_self ] -- divYear
lemma house_in {X:Feet G h}(hX:X ∈ Rad G h): carve G h X=X:= by rw [ carveΩ, ( LinearMap.mem_ker.mp hX ), map_zero, smul_zero,sub_zero ] -- Rad≥0
lemma house_grad (X:Head G (h+1)): carve G h (L X)=0:= by rw [ carveΩ,depart,map_smul,inv_smul_smul₀ (positive h |>.ne'),sub_self ]
def yard (G:Gauge)(n:ℕ): Feet G (n+1) →ₗ[ℝ] Labels.Taylor G n:= (( offShell G n ).symm).toLinearMap ∘ₗ ( ( carve G (n+1)).codRestrict (Rad G (n+1)) house )
lemma taxiY (X:Feet G (h+1)): step_in G h (yard G h X)=carve G (h+1) X:=rfl
lemma cabY {X: Feet G (h+1)}(he:X∈Rad G (h+1)): step_in G h ( yard G h X )= X:= Eq.trans (taxiY X) ( house_in he )
lemma seatI : Injective (step_in G h) := fun x y hp=> Subtype.ext ( congr_arg ( fun v:Feet G (h+1)=>v.val ) hp )
lemma coastY (X:Labels.Taylor G h): yard G h (step_in G h X)=X:= seatI (cabY ( seatR X ))
lemma dustG (X:Head G (h+1+1)): yard G h (gradS G (h+1) X)=0:= seatI (by rw [taxiY, house_grad,map_zero ])
lemma projectionY (p:E4)(t:Axis)(X:Feet G (i+1)): ( Labels.Taylor.value (yard G i X) ) t p= diagonal ((carve G (i+1) X).val t) p:= rfl
-- rad all.Tensor.Pair orientation in Plane.
end YM.MS.Theater
