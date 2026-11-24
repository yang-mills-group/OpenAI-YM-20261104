import YM.LocalTaylorR2.Grafting.Depot
/-! Polynomial along Strand on actual support. Before transfer by rung. Uniform Complex-polynomial prices at output.
 Exact affine anchor count, all site modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G} (χ:Chi) (p:H.ThinP)
local notation "Θ"=>p.val
local notation "Ω"=> (M.signs S)
open _root_.YM.Marker Merge Switch Palette MergeProof Accent GridRenewal.Rain GridApprox.Nil
open Gas Ursell Trees
variable {ι Z:Type} [Fintype ι] [DecidableEq Z] (Y:ι→Leaf R)(u:ι→ℝ)(hU:Merge.Palette.Plot Y H u)
   (B:_root_.YM.Marker.Census Z)(z:ι→ _root_.YM.Marker.Poly B)
local notation "hd"=> Pressure.temp s
local notation "P!"=> Poly B
local notation "T!"=> turnWeight Y u
variable (l:ℕ)
variable (k:H.fragrances)
local notation "Θ'"=> reachability k
local notation "T'"=> Booking H Y l k -- check args
set_option quotPrecheck false
local notation "Z₀"=> Option (Fin k.1)
open Charge RG01.Survive.Products AnalyticBridge VerifiedReset Next.Foundations
variable {j k' m' n:ℕ} {θ ρ D K e v₀ d b r x Ct b' R' A c' δ :ℝ}
variable (hk:Marker.Tinted G s K d o.a L χ j)(U:StoresR2 H j v₀ d A D k' x n χ)
variable (N:Captain H j Ct d v₀ w A b r b' R' (n+j) χ) {ζ:ℝ}(hB:LocalBookingsR2 ζ c' N.conduit)
variable (h:1≤betaF G s L)(hζ:0≤ζ)(hH:1≤θ)(hp:1≤ρ)(hs:ρ*c'≤1)(hL: Charge.Allows l j θ)(hℓ: ρ^(l+1) ≤ betaF G s L^ζ)(hM:betaF G s L^ζ ≤ Real.exp (Q.mark L μ s))
-- complex germ enough for estimating differences. Poly real smul not installed by choices? compute as complex when combining.C
open Reel (Filled Strand)
open Reel.Strand (dial)
section away
variable {W: Type*}[TopologicalSpace W]
def tint (V:W):(W→ℂ)→+* Filter.Germ (𝓝 V) ℂ:= Filter.Germ.coeRingHom _
open Reel
omit [Fintype ι]
private def wool (w:ℂ)(V:W)(x:Still V):Filter.Germ (𝓝 V) ℂ:= x.map fun x:ℝ=> x • w
private lemma wooly (w:ℂ)(V:W) (x y:Still V)(c:ℝ): wool w V (x+y)=wool w V x+ wool w V y ∧ wool w V (c • x)=c • wool w V x:= by
   induction x using Filter.Germ.inductionOn with | _ x => ?_
   induction y using Filter.Germ.inductionOn with | _ y => ?_
   have h : (fun t:W=> (x t+y t) • w)=(fun t=>x t • w)+(fun t=>y t • w):= funext fun _=> add_smul ..
   have hk : (fun t:W=> (c*x t) • w)=c • (fun t=> x t • w):= funext fun _=>mul_smul ..
   exact ⟨congr_arg (tint V) h,congr_arg (tint V) hk⟩
lemma plaster (w:ℂ)(V:W)(f:Strand→ W→ℝ) (hx:Filled ⊤ j dial (fun i=>Reel.memo V (f i))): Filled ⊤ j dial (fun i=> tint V (fun x=> f i x • w)):= hx.transfers (wool w V) (fun _ _=> Submodule.mem_top) (fun x _ y _=> (wooly w V x y 1).1) (fun x _ y => (wooly w V x x y).2)
lemma scalarG (V:W)(f:W→ℂ)(z:ℝ): tint V ((z:ℂ) • f)=z • tint V f:= by
   have ht : (z:ℂ) • f=z • f:= funext fun _=> Complex.real_smul ..|>.symm
   rw [ht]; rfl
end away
local notation "P_"=> Config G c→Poly B
variable {P':BudgetPoint} (q₁:Z→ℝ) (Rα:Z→Site c)
section comb
variable {x' v:ℝ}{u v₁:H.fragrances→ Config G c→Poly B}
omit [Fintype ι] in
lemma shopPlus (h:shop H B q₁ Rα P' u v)(hx:shop H B q₁ Rα P' v₁ x') : shop H B q₁ Rα P' (u+v₁) (v+x'):=by
   obtain ⟨a,ha,hH,hT⟩:=h; obtain ⟨b,hb,h,hQ⟩:=hx; refine ⟨a+b,ha.add hb,fun i=>?_,fun i=> ?_⟩
   · convert! budget_plus (hH i) (h i) using 1; ext j; simp only [Pi.add_apply]; split <;> ring
   obtain ⟨A,hA,hv,hF,hP⟩:= hT i; obtain ⟨D,hD,hv',hg,hp⟩:= hQ i; refine ⟨A+D,fun i=> add_nonneg (hA i) (hD i),?_,fun i=> ?_, fun i=>?_⟩ -- i shadow notation
   · change wordsPrice q₁ _ ≤ a i+b i; unfold wordsPrice; simp_rw [Pi.add_apply,mul_add,Finset.sum_add_distrib]; exact add_le_add hv hv'
   · exact ⟨Next.Foundations.regular_add (hF _).1 (hg _).1,fun x hx=> Next.Foundations.bound_add (hF _).1 (hg _).1 ((hF _).2 x hx) ((hg _).2 x hx)⟩
   exact ⟨fun j hh=> (by simp only [Pi.add_apply,Poly.part_plus,(hP i).1 j hh,(hp i).1 j hh,add_zero]),by simp only [Pi.add_apply,Poly.part_plus,(hP i).2,(hp i).2,add_zero]⟩
omit [Fintype ι] -- maybe already not included
lemma shopScale (h:shop H B q₁ Rα P' u v)(s:ℂ):shop H B q₁ Rα P' (s • u) (‖s‖*v) := by
   obtain ⟨a,ha,hH,hT⟩:=h; refine ⟨(fun i=>‖s‖*a i), ha.mul_left _,fun i=> ?_,fun i=>?_⟩
   · convert! budget_scale (norm_nonneg s) (hH i) using 1; ext j; dsimp only; split <;> ring
   obtain ⟨A,hA,hv,hF,hP⟩:= hT i; refine ⟨(fun i=>‖s‖*A i),fun i=>mul_nonneg (norm_nonneg s) (hA i), ?_, fun i=> ⟨Next.Foundations.regular_smul s (hF _).1,fun x hx=> Next.Foundations.bound_smul s ((hF _).2 x hx)⟩,fun t=>?_⟩
   · exact le_trans (le_of_eq (show wordsPrice q₁ (fun i=>‖s‖*A i)= ‖s‖*wordsPrice q₁ A from by unfold wordsPrice; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>mul_left_comm ..)) (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
   exact ⟨fun j hh=> (by simp only [Pi.smul_apply,Poly.part_smul,(hP t).1 j hh,mul_zero]),by simp only [Pi.smul_apply,Poly.part_smul,(hP t).2,mul_zero]⟩
lemma shopSub (h:shop H B q₁ Rα P' u v)(hx:shop H B q₁ Rα P' v₁ x') : shop H B q₁ Rα P' (u-v₁) (v+x'):= by simpa [sub_eq_add_neg] using! shopPlus H B q₁ Rα h (shopScale H B q₁ Rα hx (-1))
lemma shopNil : shop H B q₁ Rα P' 0 0:= by
   refine ⟨0,summable_zero,fun i=>by simp [SumBudget],fun i=> ⟨0, le_rfl,?_,fun j=> ?_,fun _=> ⟨fun _ _=> rfl,rfl⟩⟩⟩
   · simp [wordsPrice]
   have h (x:Site c) : P'.Regular (reachability i) (0:Config G c→ℂ) ∧ P'.supBounds x (reachability i) (0:Config G c→ℂ) 0 := by simpa using (Next.Foundations.regular_bound_sum (P:=P') (∅:Finset Unit) (fun _=> (0:Config G c→ℂ)) (fun _=> 0) (o:=x) (s:=reachability i) (by simp))
   exact ⟨(h 0).1,fun x _=> (h x).2⟩
lemma shopVector {Kk:Type*} (S:Finset Kk) (f:Kk→ H.fragrances→P_)(s:Kk→ℝ)(h:∀ i∈ S,shop H B q₁ Rα P' (f i) (s i)) : shop H B q₁ Rα P' (∑ i∈S,f i) (∑ i∈S,s i):=by
   induction S using Finset.induction_on with
   | empty => simp only [sum_empty]; exact shopNil ..
   | insert i S hi ih=> rw [sum_insert hi,sum_insert hi]; exact shopPlus _ _ _ _ (h i (mem_insert_self ..)) (ih fun _ hj=> h _ (mem_insert_of_mem hj))
lemma shopG (h:shop H B q₁ Rα P' u v)(hx:shop H B q₁ Rα P' v₁ x')(hp:∀ i (V:Config G c), Healthy P'.threshold (reachability i) V → ∀ m, tint V (fun U=> (u i U).part m)= tint V (fun U=> (v₁ i U).part m)): shop H B q₁ Rα P' v₁ v:=by
   obtain ⟨b,hb,hH,hT⟩:=h; refine ⟨b,hb,hH,fun i=>?_⟩
   obtain ⟨v,hv,hQ,hh,-⟩:=hT i; obtain ⟨c,-,-,hc⟩:=hx; obtain ⟨t,-,-,h,hk⟩:= hc i; refine ⟨v,hv,hQ,fun m=>⟨(h m).1,fun z hz=> ⟨((hh m).2 z hz).1,fun V he l hv hl =>?_⟩⟩,hk⟩
   rw [←AnalyticBridge.LocalGaussian.identical (Filter.Germ.coe_eq.mp (hp i V he m))]; exact ((hh m).2 z hz).2 V he l hv hl
end comb
end YM.LocalTaylorR2.Orbit
