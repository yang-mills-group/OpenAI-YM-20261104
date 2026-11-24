import YM.LocalTaylorR2.Scaling
/-!
# Purchase every Life R2 for the same trajectory (numerical gates)
 Geometry and exponent requirements are post-stage. Does not shrink output
 support norm or compare representatives through a quotient.

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
open Charge Candle Tender AnalyticBridge VerifiedReset Price
namespace Tail

structure GateR2 (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(μ s t θ D x B r c' w δ ζ:ℝ)(j l n:ℕ) : Prop where
  gamma : 1≤betaF G s L
  tPos : 1≤t
  theta : 1≤θ
  zeta : 0≤ζ
  tolerance : Charge.Allows l j θ
  spare : t*c'≤1
  contingency : t^(l+1) ≤ betaF G s L^ζ
  metric : betaF G s L^ζ ≤ Real.exp (Q.mark L μ s)
  cushion : degreePrice (radiusB s) (massb Q L μ s θ t l c') Q.δ ≤ 1/2
  limit : secondQ Q L μ s θ t D x B r c' l n j ≤ w
  orders : degreePrice (radiusB s) w δ ≤ 1/2
  quotes : 0<w

-- terminal fee already includes the installed support orientation precision. K still charged separately.
structure Election (l j n k : ℕ) (Q : YM.ConnectedActivityE6.Target G P) (L:Side)(μ W s δ:ℝ) (o:Target.Order G W) (χ:Chi)
    (A a C x d v t r B K q ρ b w θ:ℝ) : Prop where
  gates : GateR2 Q L μ s ρ θ K x B r b w δ (l+1:ℝ) j l n
  chooses : ∀ (c f:Side)(S:StepData c f) (T:Tube G S), Stamp T → ∀ (R:RG.Rep G f)(C':ℝ)(H:Cash W s μ L Q o C' T R),
    ∃ N:Captain H j C d v t A a r B q (n+j) χ, LocalBookingsR2 (l+1:ℝ) b N.conduit ∧ StoresR2 H j v d A K k x n χ
-- Note Gates hδ? consumer since δ from Expense. Criterion ties report-order `u` and `σ`, ζ etc.
def Written (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(W μ s ε δ u:ℝ)(j σ l:ℕ) (o:Target.Order G W)(χ:Chi):Prop := ∃ A a C x d v t r B K q ρ b w θ n k, Election l j n k Q L μ W s δ o χ A a C x d v t r B K q ρ b w θ ∧
    ∀ i : ℕ,i ≤ l+1 → report G j σ δ s w u ρ i ≤ betaF G s L^(requested i ε)
-- For arbitrary request P, only need the purchase in the nonvoid case
-- (the witness of Branches comes from actual H). 

theorem choosesTail (P : Teller G) (Q:YM.ConnectedActivityE6.Target G P)(Q':Target.Expense Q) : ∃ n:ℕ,∀ (L:Side), n≤L.val → ∀ W μ (o:Target.Order G W) (h k l:ℕ) (ε u:ℝ) (χ:Chi), 0<W → 0<μ → 0<ε → (∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j) →
    ∀ᶠ x in atTop, Written Q L W μ x ε (Q'.one/2) u h k l o χ:=by
  obtain ⟨N,H⟩:= curriculum P Q
  refine ⟨N,fun L hp W μ o j σ l ε U χ hW hμ hε he=>?_⟩
  obtain ⟨D,hd,hL,hJ⟩:= he
  obtain ⟨Θ,hθ,hΘ⟩:=Series.allowance l j
  obtain ⟨e,hp',he,h⟩:= plan l ε hε
  have hR: -(1/2:ℝ)< min Q.rate (-e) := lt_min Q.start (by linarith)
  obtain ⟨r,hr,hΞ⟩:= exists_between hR; obtain ⟨hS,hE⟩:= lt_min_iff.mp hΞ
  let ζ:= (l+1:ℝ)
  have hζ:1 ≤ ζ := by unfold ζ; linarith [Nat.cast_nonneg (α:=ℝ) l]
  obtain ⟨A,a,C,d,v,t,K,B,q,D',p,b,k,n,hB,hK,hb,hD,hP,hF⟩:= H L hp r ζ hr hS (zero_le_one.trans hζ) D hd j χ W hW μ hμ o
  let ρ x:=betaF G x L^e
  let u:=max Q.rate (e+r); have hu:u<0:=max_lt Q.stop (by linarith)
  obtain ⟨u',hh,h'⟩:= exists_between hu; let w x:=betaF G x L^u'
  have hI:= (incline (θ:=Θ) ρ l (show Rate G L e ρ from Rate.power) hb hμ (le_max_right ..) (le_max_left Q.rate (e+r)))
  have ht:=tangent (θ:=Θ) D' B b p K ρ l n j (show Rate G L e ρ from Rate.power) hb hμ (le_max_right ..) (le_max_left Q.rate (e+r)) hD hB hP hK
  let δ:=Q'.one/2
  have hm:= meters (t:=u') w Rate.power δ
  have hv (i:Fin (l+2)):= height (L:=L) G i j σ U e δ u' (requested i ε) (lt_trans (add_lt_of_neg_right _ h') (h i (Nat.le_of_lt_succ i.isLt))) 
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,marked (L:=L) Q hμ ζ,(meters _ hI Q.δ).below hu (1/2) (by norm_num),((Rate.power (a:=e)).mul hb).below (by linarith) 1 zero_lt_one,
    ht u' hh, hm.below h' (1/2) (by norm_num),eventually_all.mpr hv, hF] with x hx hpz hx' he' hv' hw hi hXX
  have hX:1≤ρ x:= Real.one_le_rpow hx hp'.le; have hw':0<w x:= Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
  have hg : ρ x ^ (l+1) ≤ betaF G x L^ζ:= by
    rw [show ρ x ^(l+1)=_ from (Real.rpow_mul_natCast (zero_le_one.trans hx) e (l+1)).symm]; apply Real.rpow_le_rpow_of_exponent_le hx; have hh : ((l+1:ℕ):ℝ)=ζ:=by unfold ζ; push_cast; rfl 
    rw [hh]; exact mul_le_of_le_one_left (zero_le_one.trans hζ) (by linarith)
  exact ⟨A,a,C,p x,d x,v x,t x,K x,B x,D' x,q x,ρ x,b x,w x,Θ,n,k,⟨⟨hx,hX,hθ,(zero_le_one.trans hζ),hΘ,(le_abs_self _).trans he',hg,hpz,(le_abs_self _).trans hx',(le_abs_self _).trans hv',(le_abs_self _).trans hw,hw'⟩,fun _ _ S T hT R C H=> hXX _ _ S T ((H.laws.data.funds).patch hL hJ) hT R C H⟩, fun i h=> (le_abs_self _).trans (hi ⟨i,Nat.lt_succ_of_le h⟩)⟩
end Tail
end YM.LocalTaylorR2
