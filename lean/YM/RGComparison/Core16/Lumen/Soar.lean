import YM.RGComparison.Core16.Lumen.Meter
/-!
# Inflation theorem for the tilted sensors (uniform before ι,p & all w,L,V)

The score identity by itself is not invertibility. Assemble through same-outgoing-condition family,
lengths may be requested again but stage gate independent of period. ALL interactions and branches
in that output from true integral. See deployment for instantiated readers. No analyticity θ in g
outside branch book imposed. Vital test X.g genesis recognition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals Matrix
open PertExtension PertExtension.Series Tested Radial Therm
open Stage Finset Planet Gravity
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side} {ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D]
variable {X:Shelf G A D}(P:Planet X S ι k T)

def moment (w:Rail G ι)(s:ℝ):= P.expect (dollar s) (sing w (dollar s))
def rivet (w:Rail G ι)(i:Wire G ι)(s:ℝ):=∑ j,P.plank i j* moment P (j::w) s
variable {P}{B:Stage}
set_option maxHeartbeats 400000 in
lemma form (Y:Good X) (r d:ℕ)(U:Stage){v u:ℝ}(hv:0≤v)(hu:0≤u):∃ (W:Stage)(j:ℝ), W.Above U ∧ Visit W X ∧ 0≤j ∧ ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(S:Side)(P:Planet X S ι k T), P.Steady→ Raw P U r (1+r+d) u→ Raw P U (r+1) d v → ∀ w:Rail G ι, w.length≤d →∀ i:Wire G ι,W.Ticket (r+1) j (rivet P w i) := by
    obtain ⟨b,hb⟩:= buys Y.extent.1
    obtain ⟨M,e,he,hM,hE,hte⟩:= elevator Y r d U u hu
    obtain ⟨j,T,hj,hT,hV,hJ⟩:= distill (b:=b) hb r d Y M hv hu
    let c:= weights X.sector X.sector.b*(Planet.ferris X * X.Q)
    have hc : 0≤c:=mul_nonneg (weights_pos ..|>.le) (mul_nonneg ferris_nn Y.thick.1.le)
    refine ⟨T,d*j+j+ (c*v+e),above_trans he hT,hV,by positivity,fun ι k T' _ _ _ S P H h1 h2 w hw i=> ?_⟩
    have hA : Raw P M r (1+r+d) u:= Raw.broaden h1 he (le_refl _) (le_refl _); have hB : Raw P M (r+1) d v:= Raw.broaden h2 he (le_refl _) (le_refl _)
    let F s:= P.expect (dollar s) (sing w (dollar s)*fove P i b (dollar s)); let L:=lamp_gap P i b w; let 𝒱:= moment P w
    let D s:= P.expect (dollar s) (P.dark b i * depart i (dollar s) w); let U:=rivet P w i; let z:= Gravity.tilt P i
    have hL : T.Ticket (r+1) e L:= (hte ι k T' _ _ _ S P H b hb h1 i w hw).extend hT
    have hv₀ := (hV)
    have hP w (hw:w.length≤d):= hJ ι k T' _ _ _ S P H hA hB i w hw
    have hF : T.Ticket (r+1) j F:=(hP _ hw).1; have hD : T.Ticket (r+1) (d*j) D:= dpose i H hV hj (fun j hj=> (hP j hj).2) w hw
    have hx: T.Ticket (r+1) (c*v) (fun x=> -z * 𝒱 x) := ((hB w hw).extend hT |>.scales (-z)).promote (mul_le_mul_of_nonneg_right (abs_neg z|>.trans_le (offset_cost i H)) hv)
    have hy:T.Ticket (r+1) e (fun y=> (-1:ℝ)*L y):=by simpa only [abs_neg,abs_one,one_mul] using hL.scales (-1:ℝ) -- error simpl orientation shrinks expression too
    refine ((hD.more hF).more (hx.more hy)).reload (fun s hs=>?_)
    have h:= duty hb i H (hV s hs) (dollar_pos s) w
    have hh: L s=D s + F s - (z* 𝒱 s+ U s):=by unfold L lamp_gap; dsimp only; rw [h]; rfl
    change D s+F s+(-z* _ + (-1:ℝ)* _) = U s; linarith only [hh]

def Agenda (X:Shelf G A D)(B:Stage)(r d:ℕ): Prop:= ∃ (T:Stage)(j:ℝ),0≤j ∧ T.Above B ∧ Visit T X ∧ ∀ (ι k U:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype U)(S:Side)(P:Planet X S ι k U), P.Steady→ Raw P T r d j
omit [Fintype A] in
lemma flat_stop (H:P.Steady) (U:Stage) (r:ℕ) (hp:Visit U X) : Raw P U r 0 1:=by
    intro w hw; rcases w with _|⟨j,w⟩
    · exact ((U.flat r 1).reload (fun s hs=> (burden H (hp s hs) 1).symm)).promote (by norm_num)
    simp at hw

omit [Fintype A] in
lemma start (Y:Good X) (B:Stage) (d:ℕ) : Agenda X B 0 d:=by
    let L : (Empty→G.Color)→ℝ:=fun _=>1
    obtain ⟨C,hC,h⟩:= Error.motion Y L contDiffAt_const 0 d 0 1 (by norm_num)
    obtain ⟨U,h1,h2,he⟩:= clean B (4*(0+d)) (h.and (willing Y)); refine ⟨U,C,hC,h1,fun s hs=>(he s hs).2, fun ι k U' _ _ _ S P H u hu=>?_⟩
    let p: Stuff G ι Empty:=fun j=> Empty.elim j; let f : Melody G ι:=1
    have hP:Visible X L f p 0 1:= ⟨fun g hg=> Envelope.const (1:ℝ), fun g hg x=>(abs_one (α:=ℝ)).le,∅,by simp,fun i=>Empty.elim i, fun _ _ _ _ _=> rfl⟩
    refine U.free 0 _ hC _ (fun s hs=> ?_); have ht:= (he s hs).1 S ι k U' _ _ _ P H f p hP u hu; let g:=dollar s
    rw [show Error 0 f L p g=1 from ?_,mul_one] at ht; swap; ext; simp [Error,untilB,f]
    refine ht.trans ?_; unfold rate; simp only [pow_zero]; gcongr; exact U.high.trans hs

lemma assemble (Y:Good X)(r d:ℕ)(B:Stage) : Agenda X B r d:=by
    induction r generalizing d B with
    | zero=>exact start Y B d
    | succ r IH =>
    induction d generalizing B with
    | zero=> obtain ⟨T,h,-,hk⟩:= clean B 0 (willing Y); exact ⟨T,1,zero_le_one,h,hk,fun _ _ _ _ _ _ _ _ hj=> flat_stop hj T (r+1) hk⟩
    | succ d J =>
      obtain ⟨U,c,hc,he,hy1,hU⟩:= IH (1+r+d) B
      obtain ⟨W,v,hv,hW,hy2,hw⟩:= J U
      obtain ⟨M,j,hm,hy,hj,hM⟩:= form (U:=W) Y r d hv hc
      let t:= |Planet.depthFare X| *j; have ht:0≤ t:=mul_nonneg (abs_nonneg _) hj
      refine ⟨M,v+t,add_nonneg hv ht,above_trans (above_trans he hW) hm,hy,fun ι k T _ _ _ S P H u hu=>?_⟩
      have hB : Raw P M (r+1) d v:= Raw.broaden (hw _ _ _ _ _ _ _ _ H) hm (le_refl _) (le_refl _)
      rcases u with _ | ⟨i,u⟩
      · exact (hB [] (Nat.zero_le d)).promote (le_add_of_nonneg_right ht)
      let U:=P.plank; let E:= P.plank⁻¹; let Q (x:ℝ)(i:Wire G ι):= moment P (i::u) x
      have hK : u.length ≤ d:= by simpa using hu
      have hh s:= hM _ _ _ _ _ _ _ _ H (Raw.broaden (hU _ _ _ _ _ _ _ _ H) hW (le_refl _) (le_refl _)) (hw _ _ _ _ _ _ _ _ H) u hK s
      refine ((M.ticket_sum (r+1) univ (fun q x=> E i q * rivet P u q x) (fun q=>|E i q| * j) (fun y _=> (hh y).scales _)).reload ?_).promote ?_
      · intro s hs; change (E *ᵥ (U *ᵥ Q s)) i= (Q s) i; rw [mulVec_mulVec,Matrix.nonsing_inv_mul P.plank (isUnit_iff_ne_zero.mpr (forge_plate H).det_pos.ne'),Matrix.one_mulVec]
      rw [← sum_mul]; exact (mul_le_mul_of_nonneg_right ((earmark H i).trans (le_abs_self _)) hj).trans (le_add_of_nonneg_left hv)
end YM.RGComparison.Core16.Lumen
