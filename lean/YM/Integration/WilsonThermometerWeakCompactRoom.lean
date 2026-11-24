import YM.Integration.WilsonThermometerWeakOriginalShapeGeometry

/-! Physical child and exterior room purchased on a compact set before the shrinking test is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCompactRoom
open Set Function Lattice Wilson RG Source Labels Next.Extract Next.UVStress PhysicalNext.Repeat.Legato Push StressFlux.Matching Cells
open WilsonThermometerWeakSeatedExterior (Seats padding)
open WilsonOffsetReportingProducts (Avoids)
open WilsonPositionPhysicalCellTest (Sites site cell mass)
open private visible from YM.Integration.WilsonPositionPhysicalCellTest
open MeasureTheory Filter Extraction Spec
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G}
local notation "C" => R.family
local notation "S" => R.family.S
local notation "Lev" => R.family.path.levels

open WilsonThermometerWeakShapeRoster (clearance)
open WilsonThermometerWeakOriginalShapeGeometry (fixed)
open private sampled from YM.Integration.WilsonThermometerWeakOriginalShapeGeometry
private theorem component {n:ℕ}(x:Points n)(i:Fin n)(a:Axis):|x i a|≤‖x‖:=
  (show |x i a|≤‖x i‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x i) a).trans (PiLp.norm_apply_le x i)

/-- Every original scaler is kept at its own physical displacement. At small r their
joint clearance is at least c r and their whole extent is bounded before the cutoffs. -/
theorem roster {n l:ℕ}(schedule:Schedule)(K:Set (Points n))(compact:IsCompact K)(cleared:K⊆conf n)(h:Points (l+1))(zero:h 0=0)(distinct:h∈conf _):
    ∃c:ℝ,0<c ∧ ∃B:ℝ,0≤B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0,∀x∈K,
      let q:Fin n ⊕ Fin l→E4:=Sum.elim (fun i=>(r • x) i) (fun i=>h i.succ)
      (∀i j,i≠j → ∃a:Axis,r*c≤|q i a-q j a|) ∧ ∀i j (a:Axis),|q i a-q j a|≤B:=by
  obtain ⟨γ,yp,near⟩:=clearance schedule compact cleared
  obtain ⟨t,tp,far⟩:=clearance schedule (isCompact_singleton (x:=h)) (Set.singleton_subset_iff.mpr distinct)
  obtain ⟨M,bound⟩:=compact.isBounded.exists_norm_le
  let capSize:=max 1 M
  have cp:0<capSize:=by dsimp only [capSize];positivity
  let g:=min γ (t/2)
  have gp:0<g:=lt_min yp (half_pos tp)
  have g₁:g≤γ:=min_le_left ..;have g₂:g≤t/2:=min_le_right ..
  refine ⟨g,gp,2*(capSize+‖h‖),by positivity,?_⟩
  have low:∀ᶠr:ℝ in 𝓝[>] 0,r<t/(2*capSize):=(eventually_lt_nhds (div_pos tp (by positivity))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,low,(eventually_lt_nhds (zero_lt_one:0<(1:ℝ))).filter_mono nhdsWithin_le_nhds]
    with r rp small r1
  intro x hx q
  have upper (i:Fin n)(a:Axis):|x i a|≤capSize:=(component x i a).trans ((bound x hx).trans (le_max_right ..))
  have held (i:Fin n)(a:Axis):|(r • x) i a|≤r*capSize:=by
    change |r*x i a|≤_;rw [abs_mul,abs_of_pos rp];exact mul_le_mul_of_nonneg_left (upper i a) rp.le
  have rc:r*capSize<t/2:=by have:= (lt_div_iff₀ (by positivity:0<2*capSize)).mp small;linarith
  have alone (j:Fin l):∃a:Axis,t≤|h j.succ a|:=by
    obtain ⟨a,z⟩:=far h (mem_singleton h) j.succ 0 (Fin.succ_ne_zero j)
    exact ⟨a,by simpa only [zero,PiLp.zero_apply,sub_zero] using z⟩
  have mixed (i:Fin n)(j:Fin l):∃a:Axis,g≤|(r • x) i a-h j.succ a|:=by
    obtain ⟨a,post⟩:=alone j
    have u:|h j.succ a-0|≤|h j.succ a-(r • x) i a|+|(r • x) i a-0|:=abs_sub_le .. 
    rw [sub_zero,sub_zero,abs_sub_comm (h j.succ a)] at u
    exact ⟨a,by linarith only [post,u,held i a,rc,g₂]⟩
  have rg:r*g≤g:=mul_le_of_le_one_left gp.le r1.le
  constructor
  · intro i j diff
    cases i with
    | inl i=>
      cases j with
      | inl j=>
        obtain ⟨a,h⟩:=near x hx i j (by simpa only [ne_eq,Sum.inl.injEq] using diff)
        refine ⟨a,?_⟩
        change r*g≤|r*x i a-r*x j a|
        rw [←mul_sub,abs_mul,abs_of_pos rp]
        exact mul_le_mul_of_nonneg_left (g₁.trans h) rp.le
      | inr j=>
        obtain ⟨a,h⟩:=mixed i j; exact ⟨a,rg.trans h⟩
    | inr i=>
      cases j with
      | inl j=>
        obtain ⟨a,z⟩:=mixed j i
        exact ⟨a,(rg.trans z).trans_eq (abs_sub_comm ..)⟩
      | inr j=>
        obtain ⟨a,z⟩:=far h (mem_singleton h) i.succ j.succ (by
          intro eq;exact diff (congrArg Sum.inr (Fin.succ_injective l eq)))
        exact ⟨a,rg.trans (g₂.trans ((half_le_self tp.le).trans z))⟩
  · have size (i:Fin n ⊕ Fin l)(a:Axis): |q i a| ≤ capSize+‖h‖:=by
      cases i with
      | inl i=>exact (held i a).trans ((mul_le_of_le_one_left cp.le r1.le).trans (le_add_of_nonneg_right (norm_nonneg _)))
      | inr i=>exact (component h i.succ a).trans (le_add_of_nonneg_left cp.le)
    intro i j a;exact (abs_sub ..).trans (by linarith only [size i a,size j a])

theorem original {n l:ℕ}(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(v:ℕ)(vp:0<v)
    (V:∀d,SectionData ((C).labels.level d))(d:Fin n→ℕ)(e:Fin l→ℕ)(rad:ℕ→ℕ)
    (K₀:Set (Points n))(compact:IsCompact K₀)(cleared:K₀⊆conf n)(h:Points (l+1))(zero:h 0=0)(disjoint:h∈conf _):
    ∃p₀:ℕ,∀ᶠρ:ℝ in 𝓝[>] 0,let m:=WilsonMeasuredWindow.stop (Lev) simple v ρ
      ∃N₀:ℕ,∀(p:ℕ),p₀≤p →∀N:ℕ,N₀≤N →∀s:Finset (Fin n),∀k:Fin l→ℕ,(∀i,m≤k i) →
      ∀(φ:Test n),tsupport (φ:Points n→ℂ)⊆K₀ →∀c:Sites R (N,p) n,mass φ ρ (N,p) c≠0 →
      Avoids («C» := (C)) V rad (fun i:s=>d i) (fun i=>c i) ∧
      (∀(i:s)(t:Fin l),(↑(((C).localSection (e t)).footprint (fixed (R:=R) h N p t)):Set (Site ((C).side N p)))⊆Mark.Outer (rad (d i)) (c i)) ∧
      Seats (R:=R) (m:=m) s k c (fixed (R:=R) h N p):=by
  classical
  let b:ℕ:=Finset.univ.sup (fun s:Finset (Fin n)=>padding (R:=R) (Fin l) s)+1
  have budget (s:Finset (Fin n)):padding (R:=R) (Fin l) s+1≤b:=Nat.add_le_add_right (Finset.le_sup (f:=fun s=>padding (R:=R) (Fin l) s) (Finset.mem_univ s)) 1
  obtain ⟨t,tp,B,_,shape⟩:=roster (S) K₀ compact cleared h zero disjoint
  have per:Tendsto (fun p:ℕ=>((S).period p).val:ℕ→ℕ) atTop atTop:=(S).period_strict.tendsto_atTop
  obtain ⟨p₀,room⟩:=eventually_atTop.mp ((tendsto_natCast_atTop_atTop.comp per).eventually_gt_atTop (2*(B+3*(S).a 0)))
  refine ⟨p₀,?_⟩
  have pace:=WilsonThermometerWeakCellPace.original R simple slow b v vp (t/3) (by positivity)
  filter_upwards [shape,pace] with ρ census date
  let m:=WilsonMeasuredWindow.stop (Lev) simple v ρ
  let j:=m-b
  have early (s:Finset (Fin n)):j+padding (R:=R) (Fin l) s+1 ≤ m:=by
    have:=budget s;have :=date.1;dsimp only [j];omega
  let K:=WilsonThermometerWeakRosterMargins.invoice V d e rad
  have fine:∀ᶠN:ℕ in atTop,(K:ℝ)*(S).a N<(S).a j:=
    (show Tendsto (fun N=>(K:ℝ)*(S).a N) atTop (𝓝 0) by simpa only [mul_zero] using (S).shrinks.const_mul (K:ℝ)).eventually_lt_const ((S).a_pos j)
  obtain ⟨N₀,after⟩:=eventually_atTop.mp (fine.and (eventually_ge_atTop j))
  refine ⟨N₀,?_⟩
  intro p large N late s k newer φ covers c paid
  obtain ⟨x,hx,atc⟩:=sampled φ ρ N p c paid
  have all:=census x (covers hx)
  let g:s ⊕ Fin l→Fin n ⊕ Fin l:=Sum.map (fun i:s=>i.val) id
  have faithful:Injective g:=Sum.map_injective.mpr ⟨Subtype.val_injective,injective_id⟩
  let X:s ⊕ Fin l → Lattice.Cover:=Sum.elim (fun i:s=>address ((S).a N) (ρ • x) i.val) (fun i:Fin l=>address ((S).a N) h i.succ)
  let y:Fin n ⊕ Fin l→E4:=Sum.elim (fun i=>(ρ • x) i) (fun i=>h i.succ)
  refine WilsonThermometerWeakRosterMargins.physical V d e rad s j m N p k (early s) (fun i=>(early s).trans (newer i))
    _ c X (fun i=>congrFun atc i.val) (fun i=>rfl) (y ∘ g) ?_ ((S).strictAnti.antitone (after N late).2) (after N late).1 ?_ ?_
  · intro i a
    cases i with
    | inl i=>exact coord_grid_bound ((S).a_pos N) (ρ • x) i.val a
    | inr i=>exact coord_grid_bound ((S).a_pos N) h i.succ a
  · intro i i' diff
    obtain ⟨a,dist⟩:=all.1 (g i) (g i') (fun eq=>diff (faithful eq))
    have cost:(S).a j≤(t/3)*ρ:=date.2
    exact ⟨a,(show 3*(S).a j≤ρ*t by linarith only [cost]).trans dist⟩
  · intro i i' a
    have bound:|(y (g i)) a-(y (g i')) a|≤B:=all.2 (g i) (g i') a
    have side:2*(B+3*(S).a 0)<(((S).period p).val:ℝ):=room p large
    change 2*(|(y (g i)) a-(y (g i')) a|+3*(S).a j)<_
    linarith only [bound,(S).strictAnti.antitone (Nat.zero_le j),side]

end YM.Integration.WilsonThermometerWeakCompactRoom
end
