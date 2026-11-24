import YM.RGComparison.Core16.Lumen.Soar

/-! # Uniform Visible estimator plant
Order accounts p+a in Advance. Clock-smoothing for converting to ordinary-g precisions costs
inactive at this seam. No asserting for unconditioned or unadmitted windows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals
open PertExtension PertExtension.Series Tested Radial Therm
open Stage Finset Planet Gravity
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{S:Side} {ι k T A D I L:Type} [Fintype ι][Fintype k][Fintype T][Fintype A][Fintype I][Fintype L][Fintype D]
variable {X:Shelf G A D}

-- vanish is on this stamp's *analytic atom*, not inherited from scaling the answer.
def Zeros (p:ℕ) (ψ:(L→G.Color)→ℝ):Prop:=∀ i<p,jet ψ i=0

def reads (P:Planet X S ι k T)(w:Rail G ι)(f:Melody G ι)(p:ℕ)(s:ℝ):=(dollar s)⁻¹^p* P.expect (dollar s) ((sing w * f) (dollar s))
omit [Fintype A] in
lemma legible {P:Planet X S ι k T}(H:P.Steady){ψ: (L→G.Color)→ℝ}{f:Melody G ι}{p:Stuff G ι L}{N a:ℕ}{C:ℝ}(hp: Visible X ψ f p N C)(hz: Zeros a ψ) (w: Rail G ι)(s:ℝ)(h:amen X (dollar s)): reads P w f a s=lapse P a p ψ f w s + P.expect (dollar s) ((sing w*tale p ψ a) (dollar s)):=by
    let g:= dollar s; let v i:=P.expect g ((sing w*tale p ψ i) g)
    unfold lapse; rw [Error.tribute H hp h,sum_range_succ]
    have hv i (hi:i<a):v i=0:=by rw [show v i=P.expect g 0 from ?_]; exact burden H h _; unfold v; congr 1; ext; change _* jet ψ i _=0; rw [hz i hi]; exact mul_zero _
    let U:= P.expect g ((sing w*f) g); have hg:0<g:=dollar_pos _
    change g⁻¹^a* U=g⁻¹^a*(U-(∑ x∈range a,g^x*v x + g^a*v a))+v a; rw [sum_eq_zero,zero_add, inv_pow]; field_simp; ring; intro i hi; rw [hv i (mem_range.mp hi),mul_zero]
lemma vintage (Y:Good X)(B:Stage) (ψ:I→(L→G.Color)→ℝ) (hψ:∀ i,ContDiffAt ℝ ∞ (ψ i) 0) (r a d N:ℕ){C:ℝ}(hc:0≤ C) : ∃ (U:Stage)(j:ℝ), U.Above B ∧ Visit U X ∧ 0≤j ∧ ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T) (n:Side) (P:Planet X n ι k T), P.Steady→∀ i f p, Visible X (ψ i) f p N C→Zeros a (ψ i) → ∀ w:Rail G ι,w.length≤d→ U.Ticket (r+1) j (reads P w f a):=by
    obtain ⟨T,t,ht,hT,_,h⟩:= assemble Y r (a+r+d) B
    obtain ⟨Z,z,hZ,hζ,hz,h0⟩:= accrue Y ψ hψ r a N d hc ht T
    obtain ⟨U,j,hj,hU,hν,H⟩:= assemble Y (r+1) (d+a) Z
    let C i:= presence (ψ i) X.Q a
    let c:= ∑ i,|C i|
    have hC:0≤c:=sum_nonneg fun _ _=> abs_nonneg _
    refine ⟨U,z+j*c,above_trans (above_trans hT hZ) hU,hν,by positivity,fun ι k T _ _ _ n P hP i f p hf he w hw=>?_⟩
    have hx : Offers (d+a) (C i) (sing w*tale p (ψ i) a):= by
        have hE:=(Offers.words w hw).mul (hf.uses Y a); rw [one_mul] at hE; exact hE
    refine (((h0 ι k T _ _ _ n P hP (h _ _ _ _ _ _ _ _ hP) i _ _ hf w hw).extend hU).more (hx.stints hP _ rfl hν hj (H ι k T _ _ _ n P hP))).reload (fun y hy=> (legible hP hf he w y (hν y hy)).symm) |>.promote ?_
    gcongr; exact le_trans (le_abs_self _) (single_le_sum (fun i _=> show 0≤ |C i| from abs_nonneg _) (mem_univ i))
end YM.RGComparison.Core16.Lumen
