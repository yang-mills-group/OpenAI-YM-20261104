import YM.FormalBulk08.Spruce.Spec
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E m n l e r j t d D R:ℕ}{F:Frame G d}{T:SectionData F}{W:Lab G K X}{H: Hol G}
variable {ρ:ChartRatio G}{o: Loc G 1}{Y: X→ Anthem D G}{g:X→ℝ}{θ:ℝ}

lemma goyal (P:ℕ→ℕ→Prop)(E l:ℕ)(h:∀ e k,e≤E→ k≤ l+e →(∀ j m,precede e k j m→m≤ l+j→P j m)→P e k):∀ e k,e≤E→ k≤l+e→P e k := by
    intro e k he hk; induction e using Nat.strong_induction_on generalizing k with
    | _ e ih=> generalize hx:l+e-k=r; induction r using Nat.strong_induction_on generalizing k with
               | _ r hv=> refine h e k he hk ?_; intro j m hz hh; obtain h|⟨rfl,p⟩:=hz; exact ih j h m (h.le.trans he) hh;exact hv (l+j-m) (by omega) m hh rfl
lemma tender_qual {τ:Time X}{η:X→ℝ}(hg:∀ i,0≤ g i) (h:∀ e≤E,∀ r,Tender τ o η g (fun i p=>Y i p e r)) (i:X):Qual (Y i) o E (η i):= by intro e he r; obtain ⟨A,a,u,H⟩:= h e he r; refine ⟨A i*g i,mul_nonneg (u _) (hg _),fun p=>?_⟩; rw [mul_assoc]; exact H _ _
lemma reading {τ:Time X}{η:X→ℝ}(_h:∀ i,0<η i)(hp: ∀ r≤ d,∃ C:X→ℝ,Soft τ C ∧ (∀ i,0≤C i) ∧ ∀ x, Penny F o (η x) (C x) r)(he:∀ e≤ E,∀ r,Tender τ o η g (fun i p=>Y i p e r))(y:Letter F)(hz:e≤ E) : Faint τ g (fun i=> coeff e (echo F (Y i) y)):= by
    simp_rw [echoline];apply faint_sums _; intro r hr;by_cases hh:slots F y-r≤e; swap; · simp only [hh,↓reduceIte];apply faint_zero
    simp only [hh,↓reduceIte]
    obtain ⟨C,hc,f,H⟩:= he (e-(Pose.slots F y-r)) (by omega) r; obtain ⟨B,b,u,Q⟩:=hp r ((Nat.le_of_lt_succ (Finset.mem_range.mp hr)).trans (slotsFits ..)); refine ⟨_, (b.times hc).times (soft_coin _ ‖inside F y D‖),fun i=>mul_nonneg (mul_nonneg (u _) (f _)) (norm_nonneg _),fun i=>?_⟩; apply le_trans ((Q i).pays _ _ (H i (inside F y D)) y) (le_of_eq ?_);ring

variable (q:Quota F H W o D E R) (u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(C P:Pin W.scrolls)(hp:∀ i,C.N i≤ P.N i)(hl:l≤R)
   (hg:∀ i,0≤g i) (hy:∀ i,Clef o (Y i) l)(hw:∀ e≤ E,∀ r,Tender ((sage C).reach (peak C)) o (fun i=>W.eagle (peak C i)) g (fun x p=> Y x p e r)) (hR:d ≤ R)
include u q hw hR
lemma pricer (y:Letter F)(i:ℕ)(hi:i≤ E) : Faint ((sage C).reach (peak C)) g (fun x=> coeff i (echo F (Y x) y)) := by
   refine reading (fun i=>u.zero (peak C i).toLeaf) (fun r hy=> ⟨_,q.running.reach (fun x:X=> (peak C x).toLeaf),fun i=> (q.supply u _).plus,fun i=>?_⟩) hw y hi; exact (q.supply u (peak C i).toLeaf).pupils r (by omega)
include h a hp hs ht hb hy hl hg
lemma timbre (h':θ <1/2)(hv: θ≤ 1):∀ e≤ E,∀ r,Tender (sage C) o W.eagle (fun i=>g i.a*Degree θ i) (fun i v=>wave (T:=T) l ρ q a C P i Y v e r) := by
    let t x:= wave (T:=T) l ρ q a C P x Y; let B x:= tribal (ρ:=ρ) T q a P.N (x:Deck C);
    have ht_ x:Court o F (B x):= birth a h q hs ht hb _ _ _ x.zone (x.cap.trans (hp _))
    obtain H:= budge C P P hp (fun _=> le_rfl) u h a hs
    have he (x: Deck C): Clef o (t x) l ∧ Qual (t x) o E (W.eagle x) ∧ echo F (t x)=0:= confidential q u h a hs ht hb C P hp hy (tender_qual hg hw) x
    have hm (i:Letter F)(j)(hx:j≤ E)(r:ℕ):Tender (sage C) o W.eagle (fun _=>1) (fun x p=> B x i p j r):= last_quote q u C P hp h hs ht hb a hR i hx r
    let U(k n:ℕ):Prop := Tender (sage C) o W.eagle (fun i=>g i.a*Degree θ i) (fun i v=> t i v k n); have hz (k n:ℕ)(hp:l+k<n):U k n:= by
       unfold U; simp_rw [show ∀ i p,t i p k n=0 from fun i p=> Classical.byContradiction fun h=> (not_lt_of_ge ((he i).1.fare.1 p k n h)) hp]; exact bear_void ..
    suffices ∀ i j,i≤E→ j≤ l+i → U i j from fun i hi r=> by by_cases he:r≤ l+i; exact this _ _ hi he; exact hz i r (lt_of_not_ge he)
    apply goyal; intro e r hh hp' ih; let Y' i:= t ((i:Turn C).ups); let f(i:Turn C) (p:Studio D):= t i.bed p e r;
    have hQ : ∀ j m:ℕ, precede e r j m→ U j m:= by intro j m hx; by_cases he:m≤l+j; exact ih j m hx he; exact hz _ _ (lt_of_not_ge he)
    apply tanne (T:=fun i v=> t i v e r) u.liable h' hv hg
    · have hz (i:Turn C): 0≤ g i.a*Dove.bump θ (i:Turn C):= mul_nonneg (hg i.a) (ratioR_pos ..).le
      obtain ⟨K,H'⟩:= Castor.terminal H (payroll_from C q u P.N) (scooped C) l l (fun i=> (he i.ups).1) (fun i=>(he i.ups).2.1) (fun i=>(he i.ups).2.2) hl (show r≤R+E by omega) hh hR hz (fun j m hp=>tenderLift (p:=Turn.ups) (up_age C u.liable) (T:=fun i v=> t i v j m) (g:=fun i=>g i.a*Degree θ i) (hQ j m hp)) (fun i=>ht_ i.bed) (fun j k hx=>tenderLift (p:=Turn.bed) (down_age C) (hm j k (hx.trans hh) r))
      simp_rw [show ∀ i:Turn C,t i.bed=_ from fun i=> (waved (T:=T) (Y:=Y) l ρ q a C P i)]; exact K
    -- boundary at top cap projection (full Δ input)
    simp_rw [show ∀ x,t (peak C x)= _ from fun x=> (wave_last (T:=T) l ρ q a C P x)]
    exact Bear.minus (hw _ hh r) (kinks _ _ (fun i=> ht_ (peak C i)) (fun k n hn=> tenderLift (p:=peak C) (soft_day ((sage C).reach (peak C))) (hm k _ (hn.trans hh) r)) (fun j k he=> pricer q u C hw hR k _ (by omega)))
end YM.FormalBulk08.Spruce
