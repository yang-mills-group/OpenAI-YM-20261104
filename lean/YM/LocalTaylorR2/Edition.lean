import YM.LocalTaylorR2.Bills
/-!
# Assembly of the perturbative packets in the actual motif

Expansion on the whole unforced E6 polymer basis (including Taylor on long
supports); selectors that also cut by arity/support are further choices.
Here guard expansion = no new omitted Pairs or Chains in the main and zero
if there is *any* warning, packet, or K. Such partners are handled in the
error purchase. The final slot `l+1` includes all errors. Displaced/masked
balance extends the exact sum across all configurations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves RG01.Survive PhysicalNext.Repeat
namespace Candle
variable (H : Cash W s μ L Q o C T R) (χ:Chi) {l:ℕ} (p : H.ThinP)
-- All admissible; not inferring cost outside arc. Includes longer path merely occurring in otherwise proper genre.
def vetted : Prop:= Ac.Spark H.supportP p.val ∧ troupe T R Q.halo (radiusB s) p.val
def live : Prop := vetted H p ∧ Clear p.val

def perch (l : ℕ) : Orders l := Fin.last _
def chooseSlot {p:Molecule S} (q:Paint p l):Orders l := ⟨min (l+1) (inserts q),by omega⟩
def convolve {U:Molecule S} (q:Orders l) (f:Paint U l→ℝ):= ∑ i ∈ univ.filter (fun i=> chooseSlot i=q), f i
lemma collects {U:Molecule S} (f:Paint U l→ℝ):∑ q: Orders l,convolve q f=∑ i,f i:= by
  unfold convolve; exact sum_fiberwise_of_maps_to (fun _ _=>mem_univ _) _
lemma money {U:Molecule S} (f:Paint U l→ℝ)(h:∀ i,0≤f i) {ρ:ℝ}(he:1≤ρ) :
    (∑ q:Orders l, convolve q f *ρ^q.val) ≤ ∑ i:Paint U l, f i*ρ^inserts i:=by
  let κ i:= f i *ρ^(chooseSlot i).val
  calc
    _ = ∑ q:Orders l, convolve q κ:=by
      apply Finset.sum_congr rfl; intro q _; unfold convolve; rw [Finset.sum_mul]; exact sum_congr rfl fun i hi=> congr_arg (fun e:Orders _=> f i*ρ^e.val) (mem_filter.mp hi).2.symm
    _ = ∑ i,κ i:= collects κ
    _ ≤ _:= Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (min_le_right ..)) (h i))

def script (q: Orders l)(V:Config G c):= if live H p then convolve (U:=p.val) q (fun i=> episode H χ p.val (letters H i) V) else 0
def sprig (q: Orders l)(V:Config G c):=if q=perch l then leaflet H χ V p-∑ t∈univ.erase q,script H χ p t V else script H χ p q V

lemma equality (V:Config G c) (l:ℕ): leaflet H χ V p=∑ q:Orders l, sprig H χ p q V:=by
  let z:= perch l; rw [← add_sum_erase _ _ (mem_univ z),sprig, if_pos (rfl:z=perch l), sub_add_eq_add_sub]
  have hx : ∑ i∈univ.erase z,sprig H χ p i V=∑ i∈univ.erase z,script H χ p i V := sum_congr rfl fun i hi=> if_neg (ne_of_mem_erase hi)
  rw [hx]; ring
lemma identity_zero (hl:¬live H p) {q:Orders l} (hz:q=perch l) : sprig H χ p q=fun V=> leaflet H χ V p:=by funext V; simp [sprig,script,hl,hz]
lemma quiet (hl:¬live H p) {q:Orders l} (hz:q≠perch l) : sprig H χ p q=fun _=>0:=by funext V; unfold sprig script; rw [if_neg hz,if_neg hl]
lemma dormant (hl:¬vetted H p) (q:Orders l) : sprig H χ p q=fun _=>0:= by
  have hv : ¬live H p:= fun he => hl he.1
  by_cases hp:q=perch l
  · rw [identity_zero H χ p hv hp]; funext V; exact Classical.byContradiction (fun hx=>hl (worth hx))
  exact quiet H χ p hv hp

def Items (f:Config G c→ℝ):Prop:=GaugeInvariant f ∧ Measurable f ∧ LocalOn (H.smallAt p) f
lemma indexed (q:Orders l):Items H p (sprig H χ p q):=by
  obtain ⟨hm,hL,hX⟩:= Captain.arrived (χ:=χ) p
  have ht (q:Orders l): Items H p (script H χ p q):=by
    unfold script; by_cases he:live H p; swap
    · simp_rw [if_neg he]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
    simp_rw [if_pos he]; have hx (p':Paint p.val l):= episodeSites H (letterSect H p' (H.unionP p.val) (Subset.refl _)) χ
    exact ⟨fun U V=> Finset.sum_congr rfl (fun i _=> (hx i).2.2 U V),Finset.measurable_fun_sum _ (fun i _=> (hx i).1), fun U V h=> Finset.sum_congr rfl (fun i _=> (hx i).2.1 _ _ h)⟩
  unfold sprig; by_cases he:q=perch l; swap; · simp_rw [if_neg he]; exact ht _
  simp_rw [if_pos he]
  exact ⟨fun U V=> congr_arg₂ (·-·) (hX U V) (Finset.sum_congr rfl fun i _=> (ht i).1 U V), hm.sub (Finset.measurable_fun_sum _ fun i _=> (ht i).2.1),fun U V h=> congr_arg₂ (·-·) (hL _ _ h) (sum_congr rfl fun i _=> (ht i).2.2 U V h)⟩

variable {j n:ℕ} {A b v d r B C':ℝ} {Ξ:Utopia H j v d r C' χ}
lemma realized (h:Oboe H j v B n A b Ξ) (hv:live H p) (q:Orders l) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U:E→ Config G c) (x:E) (he:Mode U x j v) (ht:Healthy (Pressure.temp s) (H.smallAt p) (U x)) :
    sprig H χ p q ∘ U =ᶠ[𝓝 x] script H χ p q ∘ U:= by
  by_cases hq:q=perch l; swap; · exact Eventually.of_forall fun _=> if_neg hq
  have hi:∀ V:Config G c, leaflet H χ V p=episode H χ p.val (compound H p.val) V:=leafEq H (isPure hv.2) hv.1.1 hv.1.2 χ
  have hh:= episodeSum (H0:=running H (p:=p.val) l) h p.2.2 he (H:=H) (compSect H p.val) (fun i=>letterSect H i _ (Subset.refl _)) ht
  filter_upwards [hh] with y hy; dsimp only [Function.comp_apply,sprig]; rw [if_pos hq]; apply sub_eq_iff_eq_add.mpr
  rw [show script H χ p q (U y)+ (∑ t∈univ.erase q,script H χ p t (U y))= _ from add_sum_erase _ (fun t=>script H χ p t (U y)) (mem_univ q),hi]; change _=∑ p':Orders l, script H χ p p' (U y)
  simp_rw [script, if_pos hv]; rw [collects]; exact hy

lemma noOvercharge {f c:Side}{S:StepData c f} {U:Molecule S} {p:Paint U l} (h:chooseSlot p≠perch l) (i:↥(logs U)) (x:ℝ): Series.split (p i) x=x^Series.rank (p i) /( (Series.rank (p i)).factorial:ℝ):= by
  have hx : Series.rank (p i)≤ inserts p:= Finset.single_le_sum (f:=fun i=> Series.rank (p i)) (fun _ _=>Nat.zero_le _) (mem_univ _)
  have ht : inserts p < l+1 := lt_of_not_ge fun hi=> h (Fin.ext (min_eq_left hi))
  unfold Series.split; rw [if_pos]; rfl; replace hp : (p i).val + 1<l+1:= hx.trans_lt ht; omega
end Candle
end YM.LocalTaylorR2
