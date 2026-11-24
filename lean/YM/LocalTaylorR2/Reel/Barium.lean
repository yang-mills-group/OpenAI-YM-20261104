import YM.LocalTaylorR2.Reel.Rebate
/-! # Actual μ & Ray configuration germs. Combine full grades, no vacuum denominator change. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Brim
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
open YM.RG01.Survive Port Candle

variable {Iota: Type*} (w:Iota→ℝ)(m m':Iota)(hm:w m=0)(hm':w m'=1)
   (y t:Reel.Scroll G f)(Q':∀ i:Iota,Cash W s μ L Q o C T (bend R (y+w i • t)))
local notation "Ω" => (fun i:Iota=> y+w i • t)
include hm hm' Q'
variable {b' t₀ u σ e d r B δ : ℝ}{k l:ℕ} (N: Captain H k b' t₀ u σ e d r B δ l χ)
include N
lemma barium (i:H.fragrances){m₀:ℕ}(F:ℕ→Prop)(hv:∀ i,F i → i ≤ m₀)(hk:m₀ ≤ n)(V:Config G c)(hs:Healthy (Pressure.temp s) (Song.perf H i) V):
     Filled ⊤ m₀ w (fun j=> memo V (fullSegments (M:=n) (fun _ q=> F q) (team H (Ω j) (χ:=χ)) i)):= by
   let W (j: Option (Fin i.1)) z (p:Orders n):= team H (Ω z) (χ:=χ) (i.2 j) p
   let a (q:(Option (Fin i.1)→Orders n)) z:= ∏ j, W j z (q j); let U:= Finset.univ.filter (fun q=> F (atGrade (M:=n) (z:=i) q))
   let X:ℝ:= (coefficient H.seam i.2/(i.1+1).factorial)
   have he z: fullSegments (fun _ q=>F q) (team H (l:=n) (Ω z) (χ:=χ)) i = X • (∑ q ∈ U, a q z):= by
      ext Y; unfold fullSegments aliquot; simp [U,X,a,W]
   simp_rw [he,memoScale,map_sum]; apply Filled.scaling
   have ht : (fun z=> ∑ i∈U, memo V (a i z))=∑ i∈U, (fun z=> memo V (a i z)):=by ext1 z; rw [Finset.sum_apply]
   rw [ht]; apply Filled.group; intro q hq; unfold a; simp_rw [map_prod]; have he : atGrade (z:=i) q ≤ m₀:= hv _ (mem_filter.mp hq).2
   refine Filled.onward (?_:Filled ⊤ (atGrade (z:=i) q) w _) he
   have hx : (fun z=> ∏ j,memo V (W j z (q j)))=∏ j,(fun z=>memo V (W j z (q j))):=by ext1 z; rw [Finset.prod_apply]
   rw [hx]; exact Filled.accumulate _ _ _ (fun j hj=> team_filled H w m m' hm hm' y t Q' N (i.2 j) V (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem (H.smallAt ∘ i.2) hj) hs) (q j) ((Finset.single_le_sum (f:=fun i=> (q i).val) (fun _ _=>Nat.zero_le _) hj).trans (he.trans hk))) Submodule.mem_top (fun _ _ _ _ => Submodule.mem_top) (scalar_prod V)

section spin
variable {V:Config G c} (θ:Seat c)
variable {Y:Type*} {wu:Y→ℝ} {ee:Y → Config G c→ℝ}
omit hm hm' Q' N
lemma tiltedG (A:ℝ)(f g:Still (θ.view V))(h:Tendsto (Seat.view θ) (𝓝 V) (𝓝 (θ.view V))):
    (f+g).compTendsto (Seat.view θ) h=f.compTendsto (Seat.view θ) h+g.compTendsto (Seat.view θ) h ∧ (A • f).compTendsto (Seat.view θ) h=A • f.compTendsto (Seat.view θ) h:= by
  induction f using Filter.Germ.inductionOn with | _ f => ?_
  induction g using Filter.Germ.inductionOn with | _ g => ?_
  exact ⟨rfl,rfl⟩
lemma rollG (h: Filled ⊤ k wu (fun t=> memo (θ.view V) (ee t)) ) : Filled ⊤ k wu (fun t=> memo V (ee t ∘ θ.view)):=by
   have ht : Tendsto (Seat.view θ) (𝓝 V) (𝓝 (θ.view V)):=(show Continuous (Seat.view (G:=G) θ) from Wilson.continuous_pull _ _).tendsto _
   exact h.transfers (fun v:Still (θ.view V)=> v.compTendsto _ ht) (fun _ _=>Submodule.mem_top) (fun _ _ _ _=> (tiltedG θ 0 _ _ ht).1) (fun x _ A=> (tiltedG θ A x x ht).2)
end spin

variable (X:Match.Alliance I H 1 0)(β:BudgetPoint) (hb:β.threshold=Pressure.temp s)
include hb
lemma cargo {m₀:ℕ}(F:ℕ→Prop)(hv:∀ i,F i→ i ≤ m₀)(hk:m₀ ≤ n)(γ:ℝ)(φ:Bool)(i:Magazine I)(θ:Seat c)(V:Config G c)(hs: Healthy β.threshold (revolve (Beam.contents I β) (θ,i)).support V):
     Filled ⊤ m₀ w (fun j=>memo V (choir (crawl H (Ω j) X χ γ n φ F) (θ,i))):=by
     unfold choir; simp only [memoScale]; apply Filled.scaling; apply rollG
     rcases i with i|i <;> dsimp only [crawl,Sum.elim]; swap; · exact Filled.steady _ Submodule.mem_top
     simp_rw [memoScale]; apply Filled.scaling; apply barium H w m m' hm hm' y t Q' N _ F hv hk
     have he : Healthy β.threshold (Beam.dashboard I i).support (θ.view V):= (θ.healthy _ _ _).1 hs
     rwa [hb,Beam.see,reconnects I X] at he
lemma asSeen {m₀:ℕ}(F:ℕ→Prop)(hv:∀ i,F i→ i ≤ m₀)(hk:m₀ ≤ n)(γ:ℝ)(φ:Bool)(i:ℕ)(V:Config G c)(hs: Healthy β.threshold ((Beam.marquee I β).reg i).support V):
     Filled ⊤ m₀ w (fun j=>memo V (sight H (Ω j) X χ γ n φ F i)):= cargo H w m m' hm hm' y t Q' N X β hb F hv hk γ φ (pennant I i).2 (pennant I i).1 V hs
end YM.LocalTaylorR2.Reel
