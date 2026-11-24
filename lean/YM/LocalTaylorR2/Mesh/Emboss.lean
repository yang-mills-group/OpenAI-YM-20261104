import YM.LocalTaylorR2.Mesh.Pennant
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
namespace Mesh
open Candle
variable (H : Cash W s μ L Q o C T R) (L' : LogIndex c f→ Port.Test T) (χ:Chi) {l:ℕ} (p : H.ThinP)
def ode (q: Orders l)(V:Config G c):= if live H p then convolve (U:=p.val) q (fun i=> episode H χ p.val (warm H L' i) V) else 0
def issue (q: Orders l)(V:Config G c):=if q=perch l then leaflet H χ V p-∑ t∈univ.erase q,ode H L' χ p t V else ode H L' χ p q V

lemma floorplan (V:Config G c) (l:ℕ): leaflet H χ V p=∑ q:Orders l, issue H L' χ p q V:=by
  let z:= perch l; rw [← add_sum_erase _ _ (mem_univ z),issue, if_pos (rfl:z=perch l), sub_add_eq_add_sub]
  have hx : ∑ i∈univ.erase z,issue H L' χ p i V=∑ i∈univ.erase z,ode H L' χ p i V := sum_congr rfl fun i hi=> if_neg (ne_of_mem_erase hi)
  rw [hx]; ring
lemma ungrown (hl:¬live H p) {q:Orders l} (hz:q=perch l) : issue H L' χ p q=fun V=> leaflet H χ V p:=by funext V; simp [issue,ode,hl,hz]
lemma fallow (hl:¬live H p) {q:Orders l} (hz:q≠perch l) : issue H L' χ p q=fun _=>0:=by funext V; unfold issue ode; rw [if_neg hz,if_neg hl]
lemma adream (hl:¬vetted H p) (q:Orders l) : issue H L' χ p q=fun _=>0:= by
  have hv : ¬live H p:= fun he => hl he.1
  by_cases hp:q=perch l
  · rw [ungrown H L' χ p hv hp]; funext V; exact Classical.byContradiction (fun hx=>hl (worth hx))
  exact fallow H L' χ p hv hp

variable (hp : ∀ j: LogIndex c f,Kept H (H.supportP (identityLog j)) (L' j))
include hp
lemma indexed (q:Orders l):Items H p (issue H L' χ p q):=by
  obtain ⟨hm,hL,hX⟩:= Captain.arrived (χ:=χ) p
  have ht (q:Orders l): Items H p (ode H L' χ p q):=by
    unfold ode; by_cases he:live H p; swap
    · simp_rw [if_neg he]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
    simp_rw [if_pos he]; have hx (p':Paint p.val l):= episodeSites H (mantle p' (fun i=> hp i.val) (H.unionP p.val) (Subset.refl _)) χ
    exact ⟨fun U V=> Finset.sum_congr rfl (fun i _=> (hx i).2.2 U V),Finset.measurable_fun_sum _ (fun i _=> (hx i).1), fun U V h=> Finset.sum_congr rfl (fun i _=> (hx i).2.1 _ _ h)⟩
  unfold issue; by_cases he:q=perch l; swap; · simp_rw [if_neg he]; exact ht _
  simp_rw [if_pos he]
  exact ⟨fun U V=> congr_arg₂ (·-·) (hX U V) (Finset.sum_congr rfl fun i _=> (ht i).1 U V), hm.sub (Finset.measurable_fun_sum _ fun i _=> (ht i).2.1),fun U V h=> congr_arg₂ (·-·) (hL _ _ h) (sum_congr rfl fun i _=> (ht i).2.2 U V h)⟩

variable {j n:ℕ} {A b v d r B C':ℝ} {Ξ:Utopia H j v d r C' χ}
lemma realized (h:Oboe H j v B n A b Ξ) (hv:live H p) (q:Orders l) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U:E→ Config G c) (x:E) (he:Mode U x j v) (ht:Healthy (Pressure.temp s) (H.smallAt p) (U x)) :
    issue H L' χ p q ∘ U =ᶠ[𝓝 x] ode H L' χ p q ∘ U:= by
  by_cases hq:q=perch l; swap; · exact Eventually.of_forall fun _=> if_neg hq
  have hi:∀ V:Config G c, leaflet H χ V p=episode H χ p.val (compound H p.val) V:=leafEq H (isPure hv.2) hv.1.1 hv.1.2 χ
  have hh:= episodeSum (H0:=runs L' (U:=p.val) (H:=H) l) h p.2.2 he (H:=H) (compSect H p.val) (fun i=>mantle i (fun i=>hp i.val) _ (Subset.refl _)) ht
  filter_upwards [hh] with y hy; dsimp only [Function.comp_apply,issue]; rw [if_pos hq]; apply sub_eq_iff_eq_add.mpr
  rw [show ode H L' χ p q (U y)+ (∑ t∈univ.erase q,ode H L' χ p t (U y))= _ from add_sum_erase _ (fun t=>ode H L' χ p t (U y)) (mem_univ q),hi]; change _=∑ p':Orders l, ode H L' χ p p' (U y)
  simp_rw [ode, if_pos hv]; rw [Candle.collects]; exact hy

omit hp
lemma lights {f c:Side}{S:StepData c f} {U:Molecule S} {p:Paint U l} (h:chooseSlot p≠perch l) (i:↥(logs U)) (x y:ℝ): absorb (p i) y x=x^Series.rank (p i) /( (Series.rank (p i)).factorial:ℝ):= by
  have hx : Series.rank (p i)≤ inserts p:= Finset.single_le_sum (f:=fun i=> Series.rank (p i)) (fun _ _=>Nat.zero_le _) (mem_univ _)
  have ht : inserts p < l+1 := lt_of_not_ge fun hi=> h (Fin.ext (min_eq_left hi))
  have hp : (p i).val + 1<l+1:= hx.trans_lt ht
  rw [absorb,if_neg (by intro h; simp [h] at hp),Series.split,if_pos (by omega)]; rfl
end Mesh
end YM.LocalTaylorR2
