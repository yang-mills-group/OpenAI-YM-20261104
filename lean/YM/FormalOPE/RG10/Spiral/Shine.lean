import YM.FormalOPE.RG10.Spiral.Loupes
import YM.FormalOPE.RG10.Ward.LatticeTurn
/-! Top raw symbols: rotation generically ONLY after testing on curl panel values! -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Spiral
open Function Wilson Lattice Gauge Precision Exterior Work.F03 Further.CorrectedLift.Compass Source Source.Drops
   PertExtension Filter RG PertExtension.LatticePT LatticePT.Projection Finset
open Next.Rank Hue Normal MvPolynomial AnalyticBridge.CouplingShape Heat.Top Further.CurvedGaussianJets.Shape
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{d:ℕ}{F: Labels.Frame G d}{n: Side}
variable {S:SectionData F}{H:Hol G}(p : Bid.pop S)(h: S.Sound H)
local notation "B" => rendered S p
local notation "Λ" => Panel Slot G
local notation "D" => topMatrix S H h p
local notation "γ" => Bid.Dir G n
private abbrev tosh (A:γ) (i:F.Index) (t:ℝ):= (t:ℂ)⁻¹^(F.grades i).2 * S.places (Pi.single i 1) 0 (represent (t • A))
include h p
lemma raw_rising (A:γ) (i:F.Index): Tendsto (tosh (S:=S) A i) (𝓝[>]0) (𝓝 (readOn A ((D).basis i))) := by
 let Q := (B).shape i; let W:= (B).columns i
 let f (p: Slot) (t:ℝ) := p.atSite (represent (t • A)) 0
 let g (p: Slot) := faceCurl (Converter.position n p) A
 have hp (p i): Tendsto (fun t:ℝ=> t⁻¹ * (f p t i)) (𝓝[>] 0) (𝓝 (g p i)):= by
   have H := slot_limit p 0 A; rw [face_here] at H
   exact (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.continuousAt.tendsto.comp H)).mono_left (nhdsWithin_mono _ (fun x hx _=> (ne_of_gt (show 0 < x from hx)) (Set.mem_singleton_iff.mp ‹_›)))
 have ht (t:ℝ): tosh (S:=S) A i t=(t:ℂ)⁻¹^(F.grades i).2 * Bid.lumin Q (fun i=>f (W i) t):= congr_arg _ (congr_fun (rend_acts h p i) _)
 unfold tosh; -- replace
 change Tendsto (fun t=> tosh (S:=S) A i t) _ _; simp_rw [ht]; obtain he := Slope.isolate Q ((B).low i) (fun t i=> f (W i) t) (fun i=>g (W i)) (fun i=> hp _ i.2)
 rw [show readOn A _ = Hue.display g ((D).basis i) from rfl,show ((D).basis i)=_ from (show ((D).basis i)= rename (τ:=Λ) (fun k=>(W k.1,k.2)) (cut (F.grades i).2 Q) from rfl),Hue.lift_panel]; exact he

omit h p in
lemma tilted (A:γ)(s:Signed)(u:poly Λ): readOn A (exchange (clockwise s) u)=readOn (Bid.pulled A s) u := by
 unfold readOn; rw [reads_val]; congr 2; funext i; unfold reads clockwise
 rw [Finsupp.linearCombination_single]; unfold Spiral.tone see; rw [pulled, sent]; simp; left; rfl
lemma turning_raw (A:γ)(s:Signed)(i:F.Index): readOn A (exchange (clockwise s) ((D).basis i)) = readOn A (∑ j:F.Index,(F.act s.ortho (Pi.single i 1) j) • ((D).basis j)):= by
 let b:= F.act s.ortho (Pi.single i 1) 
 let J:=univ.filter (fun j=> F.grades i=F.grades j);
 have he j (hj:j∉J) : b j=0:= InversionWard.Rotation.compare s (by simpa [J] using hj)
 have hb : b= ∑ j∈ J, b j • (Pi.single j 1 : F.Coeff) := by
   funext j; rw [Finset.sum_apply]; by_cases h:j∈J
   · rw [sum_eq_single_of_mem j h (fun i _ hj=> by simp [Pi.single_eq_of_ne (Ne.symm hj)])]; simp
   rw [he j h]; symm; apply sum_eq_zero; intro z hz; simp [Pi.single_eq_of_ne (show j≠z from fun h'=> h (h' ▸ hz))]
 let f:= fun t:ℝ=> ∑ j∈J,b j*tosh (S:=S) A j t
 have ht (t): tosh (S:=S) (Bid.pulled A s) i t=f t:= by
   unfold f tosh; rw [← pulled_smul,← pull_flat, SectionData.placed_signed _ h,show affine s (0:Site n) 0=0 from by simp [affine]]
   let c := S.eval_linear.mk' _; let E := expandAt 0 (represent (t • A)); change _ * (c b E) = _
   nth_rw 1 [hb]; rw [map_sum,Finset.sum_apply,mul_sum]; apply sum_congr rfl; intro j hj; rw [map_smul,Pi.smul_apply,(mem_filter.mp hj).2]; change _ * (b j * c _ E)= b j*(_ * c _ E); ring
 rw [tilted]; apply tendsto_nhds_unique (f:=f) ((raw_rising p h (Bid.pulled A s) i).congr' (Eventually.of_forall ht))
 rw [map_sum]; simp_rw [map_smul]; change Tendsto f _ (𝓝 (∑ i:F.Index, b i * _)) -- maybe binder
 rw [← sum_subset (subset_univ J) (fun i _ hi=>by rw [he i hi,zero_mul])]; exact tendsto_finsetSum _ (fun i _=> (raw_rising p h A i).const_mul _)
end YM.FormalOPE.RG10.Spiral
