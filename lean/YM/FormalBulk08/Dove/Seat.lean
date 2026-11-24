import YM.FormalBulk08.Dove.Arc

/-! Adapt solved powers. All three units of coupling in overlapping grades. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {X:Type}{G:Gauge}{K:KernelChoices}{E e r:ℕ} {ρ:ChartRatio G}{W:Lab G K X}
namespace Lab
variable (C C':Pin W.scrolls)(u:Use W ρ E)(p:∀ x,C.N x≤ C'.N x)(v:LocalRatio ρ)(hs:G.Simple)(a:hue G)
def eating (ρ:ChartRatio G)(a:hue G)(W:Lab G K X)(M:X→ℕ)(x:X)(i:ℕ): Pot G:= waken (destination (W.V x) (M x) i) (W.wood x i) (saga ρ a W x (M x) (i+1)) ρ (W.toEmpire.bill x i)
def bandK (ρ:ChartRatio G)(a:hue G)(W:Lab G K X)(M:X→ℕ)(x:X)(i:ℕ): Pence:= scalar a (eating ρ a W M x i)
include v hs
lemma zesto (N:X→ℕ)(hx:∀ x,C.N x ≤ N x)(x:Turn C): Story (eating ρ a W N x.a x.b) (pink K.penalty (location (W.V x.a) (N x.a) x.b)) := by
    have he: x.b<N x.a:= x.head.trans_le (hx _)
    -- p/C' unused
    rw [loc_land (W.V x.a) _ _ he];exact creed _ _ _ _ _ (genu (W.V x.a) _ _ ρ a v hs (N:=N x.a) he).toStory ((W.V x.a).clock.adm _) v
include p u
lemma precoat (he: e≤E)(hr:0<r)(hu:r≤e+2) : Totem (tide C) (fun _=> fame _) W.sail (bump targetPower) (fun x=> eating ρ a W C.N x.a x.b e r) (fun x=> eating ρ a W C'.N x.a x.b e r) := by
    let T(i:Turn C):=instory ρ a W C.N i.ups;let S(i:Turn C):= instory ρ a W C'.N i.ups
    have hA (i:Turn C): FrameV (T i) _:=genu (W.V i.a) (W.wood i.a) (W.toEmpire.bill i.a) ρ a v hs (N:=C.N i.a) i.head; have hB(i:Turn C): FrameV (S i) _:=genu (W.V i.a) (W.wood i.a) (W.toEmpire.bill i.a) ρ a v hs (N:=C'.N i.a) (i.head.trans_le (p _))
    have cv:= Freight_from u C; have Q:= flight_dust u C C'.N p
    by_cases hx:e=0
    · subst e
      by_cases hr':r=1
      · subst r
        simp_rw [show ∀ i:Turn C, eating ρ a W C.N i.a i.b 0 1=0 from fun i=>pillar (zesto C v hs a C.N (fun _=>le_rfl) i) _, show ∀ i:Turn C,eating ρ a W C'.N i.a i.b 0 1=0 from fun i=>pillar (zesto C v hs a C'.N p i) _];apply Aster.voids
      obtain rfl:r=2:=by omega
      have ht:= Totem_lift (g:=Turn.bed (C:=C)) (down_age C) (final_dust C C' u p v hs a 0 2 (Nat.zero_le _) (by omega) (by omega)); have hU x : Degree targetPower ((x:Turn C).bed)≤bump targetPower x:= by
         change ratioR (W.V x.a).S _ x.b _≤ ratioR (W.V x.a).S (C.N x.a) (x.b+1) _
         dsimp only [Turn.bed]; unfold ratioR; gcongr
         all_goals first
             | exact targetPower_pos.le
             | exact Schedule.a_pos ..
             | exact le_of_lt (Schedule.a_pos ..)
             |  exact div_nonneg (Schedule.a_pos ..).le (Schedule.a_pos ..).le
             | exact StrictAnti.antitone ((W.V x.a).S.strictAnti) (Nat.le_succ _)
      have hh (i:Turn C)(M:X→ℕ)(hM:∀ x,C.N x ≤ M x): eating ρ a W M i.a i.b 0 2=instory ρ a W M i.bed 0 2:= ((zesto C v hs a M hM i).ink).trans ((genu (W.V i.a) (W.wood i.a) (W.toEmpire.bill i.a) ρ a v hs (N:=M i.a) (i.head.le.trans (hM _))).ink.symm)
      simp_rw [show ∀ i:Turn C,eating ρ a W C.N i.a i.b 0 2=_ from fun i=> hh i C.N (fun _=>le_rfl),show ∀ i:Turn C,eating ρ a W C'.N i.a i.b 0 2=_ from fun i=>hh i C'.N p]; exact ht.wanes hU
    let z:Fin r:= ⟨0,hr⟩; have hBump i:= (bump_pos (C:=C) targetPower i).le
    have hw b s (hb:b≤E)(hz:1≤s)(hl:s≤b+2): Totem (tide C) (fun _=> fame _) W.stub (bump targetPower) (fun i=> T i b s) (fun i=> S i b s):= Totem_lift (g:=Turn.ups (C:=C)) (up_age _ u.liable) (final_dust C C' u p v hs a b s hb hz hl)
    obtain H:=hw e r he hr hu;obtain H1:= rise_paid (T:=T) (M:=S) cv Q hBump z H; obtain H2:= soil_paid cv Q hBump v (fun i=>(hA i).toVivid) (fun i=>(hB i).toVivid) z he (by omega) hu (fun i l hb hk _ hE=> hw i l (by unfold precede at hE;omega) hb hk)
    obtain ⟨B,b,Q1⟩:=H.left;obtain ⟨D,d,Q2⟩:=H.right; obtain ⟨U,o,u',Y⟩:=Q.left.zeal;obtain ⟨L,q,h,X1⟩:=Q.right.zeal
    convert H1.plus H2 using 1
    · ext1 i; exact rose_eq ρ (graded W.liftF (W.trail C.N) i) (W.liftU i) (W.liftH i) z (by omega) (cv.output i).le (cv.coverage i) (Q1 i) (u' i) (Y i)
    ext1 i; exact rose_eq ρ (graded W.liftF (W.trail C'.N) i) (W.liftU i) (W.liftH i) z (by omega) (cv.output i).le (cv.coverage i) (Q2 i) (h i) (X1 i)
lemma barn : Priced (tide C) (bump targetPower) (fun x=> bandK ρ a W C.N x.a x.b) (fun x=> bandK ρ a W C'.N x.a x.b) E:= by
    intro e he; obtain ⟨A,c,U,H,pA,P,Q⟩:= (punctual u C C.N (fun _=>le_rfl)).merit; simp only [bandK, scalar,coeff_mk]; exact teller_pay a U pA (Freight_from u _).output (precoat C C' u p v hs a he zero_lt_two (by omega))
end Lab
end YM.FormalBulk08.Dove
