import YM.OPE.Therm.Ribbon
/-!
# Small-interior currency above a corona, DLG test
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Portolan
open Function Set Filter RG Lattice Wilson MeasureTheory Cells
open House Cradle
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {n:Side} {G:Gauge}(T:Tiling n) {U V : Config G n} {τ t:ℝ}
local notation "𝒞" => Config G n
local notation "E" => Edge (Site n)
local notation "η" => prior G n
local notation "F" => Face (Per n)
local notation "Ex"=> Real.exp
variable (R:Rep G n)(r:ℕ)
local notation "Q"=>Stove.haloFee R r
local notation "Z₀"=> Stove.energy R r

def region (q:ℕ)(z:Site n):=halo q {z}
def coat (q:ℕ)(z:Site n): Finset E:= links (region q z)
def border (q:ℕ)(z:Site n): Support n:= region (q+Q) z
def schedule (q:ℕ)(z:Site n) : Finset F := Finset.univ.filter (fun i=>i.1∈region (q+2) z)
def essence (τ:ℝ)(q:ℕ)(z:Site n)(U:𝒞):= Ex (-(∑ y∈border R r q z,Z₀ y U))*tape (schedule q z) τ U
-- room width beyond paid patch radius q, includes enough for energy penumbra too
def parcel (q:ℕ):=q+2*Q+8

structure Attempt (τ:ℝ)(q:ℕ)(z:Site n)(f:𝒞→ℝ) (X:Finset E) : Prop where
   trunks : X⊆ coat q z
   warm : fence (coat q z) f
   unitBound U : ‖f U‖ ≤ 1
   hb : Measurable f
   lands (U:𝒞) : press X (fun U=> f U * essence R r τ q z U) U=0

variable {R r}
variable (hv:T.kind=.site){C a:ℝ} (Y: Stove.Chart R r C a) {z:Site n} {q:ℕ} {i:T.Cell}
lemma tapes_non (τ:ℝ)(J:Finset F)(U:𝒞): 0≤ tape J τ U:=by unfold tape;split<;> norm_num
include Y
lemma essence_env : Envelope (essence R r τ q z):= ((Envelope.neg (Envelope.sum (border R r q z) Z₀ (fun i=>⟨Y.bill i,C,Y.paid i⟩))).exp).mul (tape_env _)
omit Y in
lemma region_mem {z' : Site n} : z'∈ region q z ↔ separation z z' ≤ q:=by simp [region,halo_spec]
omit Y in
lemma region_increase {r':ℕ} (h:q≤r'): region q z ⊆ region r' z:= fun _ hu=> region_mem.mpr ((region_mem.mp hu).trans h)
omit Y in
lemma link_mono {X Y:Set (Site n)}(h:X⊆Y) : links X⊆ links Y:=fun _ hu=> linn.mpr (by obtain ⟨hp,hP⟩:= linn.mp hu; exact ⟨h hp,h hP⟩)
variable {A:Finset (Edge (Site n))}
omit Y in
lemma orbits {s t:ℕ}{y:Site n}(h:s+t < separation y z): Disjoint (coat s y) (coat t z):=by
   refine Finset.disjoint_left.mpr (fun e he hu=>?_); obtain ⟨hp,hP⟩:=linn.mp (show e∈links (n:=n) (region s y) from he); obtain ⟨hq,hQ⟩:=linn.mp (show e∈links (n:=n) (region t z) from hu); exact (not_lt_of_ge ((separation_triangle _ e.1 _).trans (Nat.add_le_add (region_mem.mp hp) ((separation_comm e.1 z).trans_le (region_mem.mp hq))))) h
section isolate
include hv
variable (he:z∈lease T i (parcel R r q))
include he
omit Y in
lemma seats : (region (q+4) z : Set _) ⊆ T.chamber i := fun x hx=> deeds T hv (r:=parcel R r q) (by unfold parcel; omega) (lt_of_le_of_lt (region_mem.mp (show x∈region (q+4) z from hx)) (by unfold parcel; omega)) he
omit Y in
lemma room_bill : coat q z ⊆ edges T i := fun x hx=> House.books T (link_mono (X:=(region q z:Set (Site n))) (Y:=T.chamber i) (fun x hx=> seats T hv he (region_increase (Nat.le_add_right q 4) hx)) hx)
omit Y in
lemma pegs : border R r q z ⊆ chute T R r i := by
   intro x hx; let u:=region_mem.mp (show x∈ region (q+Q) z from hx); apply tending T hv (q:=q+Q) ?_ u; refine gesture T ?_ he; unfold parcel; omega
omit Y in
lemma enlist : schedule q z ⊆ countables T i:=by
   intro x hx; apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, fun u hu=>?_⟩; apply (host T).mpr; refine enters T (seats T hv he (region_mem.mpr (le_trans (separation_triangle _ x.1 _) ?_))); have ht:=region_mem.mp (show x.1 ∈ region (q+2) z from (Finset.mem_filter.mp hx).2); have hf := Work.E01.sep_touched x _ hu; omega
-- disjoint proof for faces unaffected
lemma outside (h:A⊆ coat q z) : ∃ F':𝒞→ℝ, (stills A F') ∧ Envelope F' ∧ (∀ U, 0 ≤ F' U) ∧ ∀ U, cell T R r τ i U= F' U * essence R r τ q z U:=by
   let S:=border R r q z; let P:=chute T R r i; let D:=P\S; let f(U:𝒞):=-(∑ x∈D,Z₀ x U); let H:=countables T i; let J:=schedule q z; let G₀:=H\J
   have he' : J⊆H:= enlist T hv he; have hT : S⊆P:=pegs T hv he
   have ht x (hx:x∈ D): stills A (Z₀ x):=by
      refine spares (local_fence.mpr (Y.home x)) (Disjoint.mono_right h ?_); apply orbits (s:=Q) (t:=q); rw [add_comm,separation_comm]; exact lt_of_not_ge (fun he=> (Finset.mem_sdiff.mp hx).2 (region_mem.mpr he))
   have hu x (hx:x∈G₀) : Disjoint A (links (↑(touched x):Set _)):=by
      refine Disjoint.mono_left h (Finset.disjoint_left.mpr fun e h₁ h₂=>?_); apply (Finset.mem_sdiff.mp hx).2; apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,region_mem.mpr ((separation_triangle _ e.1 _).trans ?_)⟩; exact Nat.add_le_add (region_mem.mp ((linn.mp h₁).1)) ((separation_comm e.1 x.1).trans_le (Work.E01.sep_touched x e.1 (linn.mp h₂).1))
   refine ⟨fun U=>Ex (f U)*tape G₀ τ U, fun U V hp=>?_, Envelope.mul (Envelope.exp (Envelope.neg (Envelope.sum _ _ fun i=>⟨Y.bill i,C,Y.paid i⟩))) (tape_env G₀),fun U=>mul_nonneg (Real.exp_pos _).le (tapes_non ..),fun U=>?_⟩
   · unfold f; dsimp only;  rw [show (∑ x∈D, Z₀ x U)=(∑ x∈D,Z₀ x V) from Finset.sum_congr rfl fun i hi=> ht i hi U V hp, still_tape hu U V hp]
   unfold cell gaugeW cup; change Ex (-(∑ x∈P,Z₀ x U))*tape H τ U=_; have hh : tape H τ U=tape G₀ τ U*tape J τ U:=by rw [← tapes, Finset.sdiff_union_of_subset he']
   dsimp only; rw [hh, ← Finset.sum_sdiff hT, neg_add,Real.exp_add]; unfold essence f G₀ D J S H P; ring

lemma approved {f:𝒞→ℝ} (H: Attempt R r τ q z f A) (U:𝒞) : press A (fun U=> f U * cell T R r τ i U) U=0:=by
   obtain ⟨g,hg,-,-,hh⟩:=outside (τ:=τ) T hv Y he H.trunks; simp_rw [hh, mul_left_comm (f _), pressmulL (h:=hg),H.lands,mul_zero]
end isolate
end YM.OPE.Therm.Portolan
