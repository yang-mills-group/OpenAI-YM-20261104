import YM.Integration.WilsonThermometerWeakCellPace
import YM.Integration.WilsonThermometerWeakRosterMargins
import YM.Integration.WilsonThermometerWeakShapeRoster
import YM.Integration.WilsonMacroscopicRichWatchPlot

/-! The actual scheduled stop clears all source and stationary exterior footprints on
every occupied physical cell. The period threshold precedes the ultraviolet limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakOriginalShapeGeometry
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

def fixed {l:ℕ}(h:Points (l+1))(N p:ℕ)(i:Fin l):Site ((C).side N p):=
  wrap ((C).side N p) (address ((S).a N) h i.succ)

theorem installed (W:Watch (C)){N p:ℕ}(live:W.t≤N)(i:Fin W.n):
    fixed (R:=R) W.held N p i=W.among N p i:=by
  change ceilSite R.family N p (W.held i.succ)=_
  have pos:W.held i.succ=(S).gridPoint W.t (W.x i):=by
    simp [Watch.held,Watch.table,Extraction.Order.grid,points]
  rw [pos]
  exact WilsonMacroscopicRichWatchPlot.grid W.t N p live (W.x i)

private theorem sampled {n:ℕ}(φ:Test n)(ρ:ℝ)(N p:ℕ)(c:Sites R (N,p) n)
    (paid:mass φ ρ (N,p) c≠0):∃x∈tsupport (φ:Points n→ℂ),site ρ (N,p) x=c:=by
  by_contra! no
  apply paid
  calc
    _ = ∫x in cell (R:=R) ρ (N,p) c,(0:ℂ):=setIntegral_congr_fun (visible ρ (N,p) c) (fun x hx=>
      image_eq_zero_of_notMem_tsupport (fun used=>no x used hx))
    _ = 0:=by simp

theorem original {n l:ℕ}(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(v:ℕ)(vp:0<v)
    (V:∀d,SectionData ((C).labels.level d))(d:Fin n→ℕ)(e:Fin l→ℕ)(rad:ℕ→ℕ)
    (φ:Test n)(h:Points (l+1))(zero:h 0=0)(disjoint:h∈conf _):
    ∃p₀:ℕ,∀ᶠρ:ℝ in 𝓝[>] 0,let m:=WilsonMeasuredWindow.stop (Lev) simple v ρ
      ∃N₀:ℕ,∀(p:ℕ),p₀≤p →∀N:ℕ,N₀≤N →∀s:Finset (Fin n),∀k:Fin l→ℕ,(∀i,m≤k i) →
      ∀c:Sites R (N,p) n,mass φ ρ (N,p) c≠0 →
      Avoids («C» := (C)) V rad (fun i:s=>d i) (fun i=>c i) ∧
      (∀(i:s)(t:Fin l),(↑(((C).localSection (e t)).footprint (fixed (R:=R) h N p t)):Set (Site ((C).side N p)))⊆Mark.Outer (rad (d i)) (c i)) ∧
      Seats (R:=R) (m:=m) s k c (fixed (R:=R) h N p):=by
  classical
  let b:ℕ:=Finset.univ.sup (fun s:Finset (Fin n)=>padding (R:=R) (Fin l) s)+1
  have budget (s:Finset (Fin n)):padding (R:=R) (Fin l) s+1≤b:=Nat.add_le_add_right (Finset.le_sup (f:=fun s=>padding (R:=R) (Fin l) s) (Finset.mem_univ s)) 1
  obtain ⟨t,tp,B,_,shape⟩:=WilsonThermometerWeakShapeRoster.original (S) φ h zero disjoint
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
  intro p large N late s k newer c paid
  obtain ⟨x,hx,atc⟩:=sampled φ ρ N p c paid
  have all:=census x hx
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

end YM.Integration.WilsonThermometerWeakOriginalShapeGeometry
end
