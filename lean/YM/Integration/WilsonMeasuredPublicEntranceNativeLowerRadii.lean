import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerUniform
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRadii
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS PhysMS.Frame
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPhysicalStationGradedLowerPanel (left right frame)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free)
open WilsonMeasuredPublicEntranceNativeLowerLeft (ears coefficients representative)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel row pivot vote)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
local notation "D" => Table.Field (Bel R.family.book)

theorem original {r t:ℕ→ℝ}{s δ:ℝ}(small:0<δ)(near:Tendsto r atTop trail)(ratio:Tendsto t atTop (𝓝 s))
    (positive:∀n,0<r n)(band:∀n,t n∈Icc (1/2:ℝ) 1)(separate:∀ᶠn in atTop,t n<1):
    ∃shift:ℕ→ℕ,Tendsto shift atTop atTop ∧ ∃outer inner:ℕ→Ioc (0:ℝ) δ,
      (∀n,(outer n:ℝ)=r (shift n) ∧ (inner n:ℝ)=t (shift n)*r (shift n)) ∧
      Tendsto (fun i=>(outer i:ℝ)) atTop (𝓝 0) ∧ Tendsto (fun i=>(inner i:ℝ)) atTop (𝓝 0) ∧
      (∀ᶠn in atTop,(inner n:ℝ)<outer n) ∧ (∀n,(outer n:ℝ)≤2*(inner n:ℝ)):=by
  have shrink:Tendsto r atTop (𝓝 0):=near.mono_right inf_le_left
  obtain ⟨first,live⟩:=eventually_atTop.1 (shrink.eventually_lt_const small)
  let shift (n:ℕ):=first+n
  have cofinal:Tendsto shift atTop atTop:=tendsto_atTop.2 fun b=>(eventually_ge_atTop b).mono fun n ge=>by
    dsimp [shift];omega
  let outer (n:ℕ):Ioc (0:ℝ) δ:=⟨r (shift n),positive _,(live _ (Nat.le_add_right first n)).le⟩
  have gt (n:ℕ):0<t (shift n):=lt_of_lt_of_le (by norm_num) (band _).1
  let inner (n:ℕ):Ioc (0:ℝ) δ:=⟨t (shift n)*(outer n:ℝ),mul_pos (gt _) (outer n).2.1,
    (mul_le_of_le_one_left (outer n).2.1.le (band _).2).trans (outer n).2.2⟩
  have fade:Tendsto (fun i=>(outer i:ℝ)) atTop (𝓝 0):=shrink.comp cofinal
  refine ⟨shift,cofinal,outer,inner,fun _=>⟨rfl,rfl⟩,fade,?_,?_,?_⟩
  · change Tendsto (fun i=>t (shift i)*(outer i:ℝ)) atTop (𝓝 0)
    simpa only [Function.comp_def,mul_zero] using (ratio.comp cofinal).mul fade
  · exact (cofinal.eventually separate).mono fun n lt=>mul_lt_of_lt_one_left (outer n).2.1 lt
  · intro n
    change (outer n:ℝ)≤2*(t (shift n)*(outer n:ℝ))
    nlinarith only [mul_nonneg (sub_nonneg.mpr (band (shift n)).1) (outer n).2.1.le]

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRadii
end
