import YM.FVA2.Position.Walks
/-!
# Marked PM solver preserves the needed interpolation estimates on rotation

See `frameQ`. This and linearity results enable averaging the mark `Acts`.
No multiplying the completed estimate by a possibly uncontrolled regulator calibration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Crosswind
open Function Set Filter Finset MeasureTheory Lattice
open MS MS.Plane MS.Tone MS.Koszul MS.Heat MS.Book MS.Landau MS.Landau.Detect MS.Momentum MS.Plane.Wire
open MS.Native MS.Native.Wilsonian MS.City MS.Tone.Frame MS.Arts MS.Arts.Spin MS.Outlook MS.Color
open Brass MS.Wind MS.High MS.High.Knobs MS.LogTime MS.LogTime.IntervalFamily
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n d:ℕ}{J:Type}{G:Gauge}{u:ℤ}(s:Signed)
variable {p:Book.Program.Team}{F H X:Dec G}{A B:Actor G}
lemma pm₀ (F:Dec G): Wind.PM 0 F 0 u := by
 refine ⟨fun _=> Fees.zero ..,?_⟩; intro i x; refine ⟨(map_zero _).symm, fun j l=>?_⟩; simp only [path,Pi.zero_apply,map_zero,one_smul,Finset.sum_apply, Finset.sum_const_zero, zero_add]; exact hasDerivAt_const j (0:ℂ)
lemma pm_plus (h:Wind.PM A F H u)(hp: Wind.PM B F X u): Wind.PM (A+B) F (H+X) u := by
    refine ⟨fun i=> (h.owes i).sum2 (hp.owes i),?_⟩; intro i x; obtain ⟨hq,ht⟩:=h.recu i x; obtain ⟨hw,hC⟩:=hp.recu i x; have he: path 1 i 0 F (H+X) = path 1 i 0 F H+path 1 i 0 F X:= by unfold path; simp only [one_smul]; funext y; simp only [Finset.sum_apply,Pi.add_apply,map_add,Finset.sum_add_distrib]
    simp only [he,Pi.add_apply]; refine ⟨?_,fun v=>?_⟩; · rw [Pi.add_apply,hq,hw,map_add]
    rw [map_add, Pi.add_apply,Pi.add_apply, ← add_add_add_comm]; exact (Zip.add (ht v) (hC v)) -- Lean class.
lemma pm_smul (c:ℝ)(h:Wind.PM A F H u): Wind.PM (c • A) F (c • H) u:= by
    refine ⟨fun i=> (h.owes i).fare c,?_⟩; intro i x; obtain ⟨hp,hu⟩:= h.recu i x; change Sat (Tone.run ( ( c:ℂ ) • A x i )) ( ( c:ℂ ) • H i x) (path 1 i 0 F ( (c:ℂ ) • H ) x); rw [ show path 1 i 0 F ((c:ℂ) • H) x=(c:ℂ) • path 1 i 0 F H x from ?_ ]; swap; · simp only [path,one_smul,map_smul, Pi.smul_apply,Finset.sum_apply,Finset.smul_sum]
    refine ⟨ by rw [map_smul,Pi.smul_apply,hp],fun v=>?_⟩; rw [map_smul, Pi.smul_apply,Pi.smul_apply,← smul_add]; exact Zip.scalar (hu v) _
lemma pm_sweep {A:J→Actor G}{K:J→Dec G}(q:Finset J)(h:∀ i∈q,Wind.PM (A i) F (K i) u)(a:J→ℝ): Wind.PM (∑ i∈q,a i • A i) F (∑ i∈q,a i • K i) u:= by
 induction q using Finset.induction with| empty=> simp only [Finset.sum_empty]; exact pm₀ F | insert i q hi ih=> rw [Finset.sum_insert hi, Finset.sum_insert hi ]; exact pm_plus (pm_smul _ (h i (by simp))) (ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
-- linear at answer *only* marks. $Trust$ convergence quantitative for all windows.
variable {f g a b: High.Recount G}
lemma fixed₀ (r:ℤ) : Fixed (0:Recount G) 0 false r d:= by intro n h m hm; exact High.zero_ext (fun _ _ _ _=>rfl) (fun _ _ _ _=>rfl)
lemma fixed_add (h:Fixed f g false u d)(he:Fixed a b false u d) : Fixed (f+a) (g+b) false u d:= by intro n hn r hr E _ _ w hw ht; exact Light.add ( h n hn r hr E w hw ht ) ( he n hn r hr E w hw ht )
lemma fixed_fare (h:Fixed f g false u d)(x:ℝ) : Fixed (x • f) (x • g) false u d:= by intro n hn r hr E _ _ w hw ht; exact Light.scalar ( h n hn r hr E w hw ht ) (x:ℂ)
lemma fixed_sum {f g:J→Recount G}(q:Finset J)(h:∀ i∈q,Fixed ( f i) (g i) false u d)(a:J→ℝ) : Fixed (∑ i∈q,a i • f i ) (∑ i∈q,a i • g i) false u d:= by
 induction q using Finset.induction with| empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact fixed₀ _| insert i q hi ih=> rw [ Finset.sum_insert hi, Finset.sum_insert hi ]; exact fixed_add (fixed_fare (h i (by simp)) _) (ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
lemma col_sum {X:J→ Dec G}(q:Finset J)(a:J→ℝ): col (∑ i∈q,a i • X i) = ∑ i∈q,a i • col ( X i):= by funext i y; simp only [col,Finset.sum_apply, Pi.smul_apply]
-- rotate, no coupling rescale. Light on primary.
lemma frameQ (h:Fixed f g false u d) : Fixed (fun n=> α s ∘ f n) (fun n=> α s ∘ g n) false u d := by
    intro n hn r hx E _ _ w hw ht; let x:= Park.spoor (m:=0) s w; have he : x.length=r:= by unfold x Park.spoor; simpa only [List.length_map];
    have hc : fieldDim wfield x=fieldDim wfield w:= by unfold x Park.spoor fieldDim; rw [List.map_map]; congr 1
    let K (f:Recount G):= Plane.lane meet (α s ∘ f n); let S:= meet.primary; let Jc:= ContinuousLinearMap.mul ℝ ℂ (↑(Brass.Track (m:=0) s (sail w 0)):ℂ);
    have hm (p:Recount G): Chart (K p) w=(fun i=>Jc ∘ Chart (Plane.lane meet (p n)) x i):= by
       funext j p0; unfold K Chart Plane.lane; simp only [comp_apply, αcash s ]; rw [ Brass.evaluate s (m:=0), Park.trace_p s (m:=0) w p0 0, Park.sails s (m:=0) w ]; rfl
    unfold Light; rw [← hc,show Chart _ w=_ from hm f,show Chart (K g) w=_ from hm g]; exact Like.L (h n hn r hx E x (fun q=> Bool.noConfusion q) he) Jc -- argument order.
end YM.FVA2.Position.Crosswind
