import YM.Integration.WilsonOriginalPublicRelativeGramNativePivot

/-! The real public reflected pair at the original optics ruler and on its
translated printed K board, with both ordered cutoff limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativeMeasure
open Filter Set Function Lattice Wilson RG Source OPE Extraction RG17 Table Spec Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Cirrus
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open WilsonOriginalPublicRelativeGramNativePivot (Ruler)
open WilsonOriginalPublicRelativeGramNativeSites (sample)
open WilsonOriginalPublicRelativeGramPins (cutoff physical)
open WilsonOriginalBlissMixedGram (grades columns)
open scoped Topology Classical BigOperators Matrix Matrix.Norms.Operator

def beam {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)(D:XSpace.Run)
    (avoid:Finset E4)(L:Ruler R D)(Y:ℝ → (ℕ×ℕ) → Glyph B h → R.family.label h)
    (p:ℝ×(ℕ×ℕ))(i j:Glyph B h):ℂ:=
  R.family.ensemble (grades h h)
    (fun u=>Cells.location R.family.S (L.top p.1) p.2.1 p.2.2
      ((sample R avoid (pointsAt a) (D.step (L.mesh p.1)) (L.live p.1) (L.scale p.1) (L.scale p.1)).layout u))
    (columns R a h h (Y (L.scale p.1) p.2 i) (Y (L.scale p.1) p.2 j))

variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)(D:XSpace.Run)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ→ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g) (L:Ruler R D)
local notation "I" => Glyph B h
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "real" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))
variable (Y:ℝ→(ℕ×ℕ) → Glyph B h →   R.family.label h)

theorem finite {r:ℝ}{z:ℕ×ℕ}(before:L.top r≤z.1)(ready:R.family.ref h≤z.1)
    (site:L.place r=Γ.date (L.scale r)):
    (beam B h a R D avoid L Y (r,z):Matrix I I ℂ)=
      entered B h a R F ℓ avoid Γ Y (L.scale r,z):=by
  classical
  ext i j
  unfold entered cutoff physical beam
  simp only [Fintype.sum_unique,one_mul]
  rw [←site]
  exact WilsonOriginalPublicRelativeGramNativeLaw.original R avoid (pointsAt a) (D.step (L.mesh r))
    (L.live r) before z.2 _ _ _ _ (fun u=>by fin_cases u <;> exact ready)

theorem ordered_map {s:ℝ→ℝ}(small:Tendsto s trail trail):
    Tendsto (fun p:Z=>(s p.1,p.2)) real real:=by
  intro u hu
  change ∀ᶠr in trail,∀ᶠz in (ℓ:Filter (ℕ×ℕ)),(s r,z)∈u
  exact small.eventually (show ∀ᶠr in trail,∀ᶠz in (ℓ:Filter (ℕ×ℕ)),(r,z)∈u from hu)

theorem original (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (b:ℝ → Glyph B h →   R.family.label h)(registered:∀ᶠs in trail,
      (∀i:Glyph B h,Tendsto (fun z=>Y s z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b s i))) ∧
      ∀i:Glyph B h,S.project h (b s i)=J s h (named R B h i))
    (site:∀ᶠr in trail,L.place r=Γ.date (L.scale r)):
    Tendsto (fun p:Z=>(beam B h a R D avoid L Y p:Matrix I I ℂ)) real (𝓝 (maxwell B h a)):=by
  have truePair:=WilsonOriginalPublicRelativeGramReflectedLimit.original B h a R F J ℓ avoid Γ simple
    temperature lead below Y b registered
  apply (truePair.comp (ordered_map ℓ L.small)).congr'
  change ∀ᶠr in trail,∀ᶠz in (ℓ:Filter (ℕ×ℕ)),_ = _
  filter_upwards [site] with r atGrid
  filter_upwards [WilsonOriginalPublicRelativeGramNativeLaw.reference ℓ below (L.top r),
    WilsonOriginalPublicRelativeGramNativeLaw.reference ℓ below (R.family.ref h)] with z atK atRef
  exact (finite B h a R D F ℓ avoid Γ L Y atK atRef atGrid).symm

end YM.Integration.WilsonOriginalPublicRelativeGramNativeMeasure
