import YM.Contacts.Tempo.Kite
namespace YM.Contacts.Tempo
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Harrier Harrier.Transfer Parcel Planned.PrimaryIntegral295
open Cartons Tensor Place Carrier MultiNext.SignedSource Pattern Barrage Barrage.Reserve.Oasis Analysis
variable {A: Ink G h M} {S:Boom} {e:Parcel G}{s:Parcel.Step}{K j':ℕ}
namespace Grounds
variable (T:Grounds A e S s K k D ζ) {x:Dye G}
local notation "Γ" => terrain ζ (Dye G)
local notation "Η" => terrain (2*ζ) (Dye G)
local notation "η" => bath ζ k (Dye G)
local notation "τ" => hop e s M h
local notation "R" => play h M e s
variable {F P:Sketch G}{V:Badge A.prism→Sketch G}{v:Badge A.prism}
namespace Critical
-- shadow all costs below horizon
variable (H:Critical e s M h D k ζ x F K) (U:Critical e s M h D k ζ x P K)
include H
include T -- D shadow remove
lemma along (u:Badge A.prism)(hi:i≤ K):Soles (placed e s A F i u):= by
    let Z(n:ℕ):= R F n; obtain ⟨c,hc,C⟩:= Pocket.key_exp i u.slot (D:=D) u T.lic.light rfl (second A u); refine Road.up (H.rolling _ u.slot hi) (P:=fun (_:Unit) n=> Issued η D x (Z n) i u.slot) (?_) hc; exact fun _ n b hb h=> C x (Z n) ((T.own H.life _).lower T.lic.down) b hb (issued_down h)
lemma hush (hi:i≤K) (hq:Harrier.Before η D x F i r 0) : ∀ (u:Badge A.prism),u.slot=r→u.win<h→ ∀ n,placed e s A F i u n=0:= by
   let RR:=placed e s A F i -- notation conflict
   let U(j:ℕ):=∀ (u:Badge A.prism),u.slot=r→u.win=j→j<h→∀ n,RR u n=0; suffices ht:∀ j,U j by exact fun v he hv n=> ht v.win v he rfl hv n
   intro j; induction j using Nat.strong_induction_on with|h j ih=>
   intro u hu hx hh; let Y:=Grounds.grindStep e s A F i u; have ht: u.win<h:=hx.trans_lt hh; have hY:Y=0:= by
       funext n; unfold Y grindStep shout; rw [T.poor x u (T.own H.life _) (by rw [hu]; exact T.pre_echo hi H.life hq) hi]; let f:=hop e s M h; rw [add_zero]; exact Finset.sum_eq_zero (s:=stress u) (fun v hv=> by obtain ⟨hw,hk⟩:= (stress_mem u v).mp hv; have he:v.win<j:=hk.trans_eq hx; exact mul_eq_zero_of_left (ih v.win he v (hw.trans hu) rfl (lt_trans he hh) n) _)
   let J:= Critical.along T H u hi; -- order ambiguous
   have hr:Runs (power s A u) (fun (_:Unit)=>Y) (fun _ n=> (0:ℝ)):= fun _ n=> by simp only [hY,Pi.zero_apply,mul_zero,add_zero]
   intro n; exact congr_fun (congr_fun (Rates.sole J Rates.zero (stress_cut s u ht) (T.tollRuns x F u) hr) ()) n
lemma solo (hi:i ≤ K)(hQ:Harrier.Before η D x F i r 0)(u:Badge A.prism)(hx:u.slot=r)(hv:u.win=h) : ∀ n, placed e s A F i u n=u.key F M i:= by
   let RR:=placed e s A F i; have H'(n:ℕ):grindStep e s A F i u n=0:= by
       unfold grindStep shout; rw [T.poor x u (T.own H.life _) (by rw [hx]; exact T.pre_echo hi H.life hQ) hi]; rw [add_zero]; exact Finset.sum_eq_zero (s:=stress u) (fun v hp=> by obtain ⟨hp,he⟩:= (stress_mem u v).mp hp; exact mul_eq_zero_of_left (hush T H hi hQ v (hp.trans hx) (he.trans_eq hv) n) _)
   intro n; induction n with|zero=>rfl|succ n ih=>rw [show placed e s A F i u (n+1)=_ from T.tollRuns x F u () n]; change power s A u * placed e s A F i u n + grindStep e s A F i u n = _; rw [H' n,bright u s hv,one_mul,add_zero,ih]
include U
lemma both_sub : Critical e s M h D k ζ x (F-P) K:= by
    refine ⟨H.life.sub U.life,fun i r hi=> ?_⟩; obtain ⟨a,b,hb,h⟩:= H.rolling i r hi; obtain ⟨c,g,hg,Z⟩:= U.rolling i r hi; refine ⟨a+c,b+g,add_nonneg hb hg,fun p n=>?_⟩; let Q:= Tempo.toll (Grounds.fixed p) n; have he:= h p n; have hk:= Z p n; change Issued η D x (R (F-P) n) i r ((b+g)*Q (a+c)); rw [T.play_sub H.life U.life]; exact issued_mon (show Issued _ _ _ _ _ _ (b*Q a+g*Q c) from ⟨before_sub x he.1 hk.1,w_sub he.2 hk.2⟩) ((add_le_add (mul_le_mul_of_nonneg_left (toll_long _ _ (show a≤ a+c by omega)) hb) (mul_le_mul_of_nonneg_left (toll_long _ _ (show c≤ a+c by omega)) hg)).trans_eq (add_mul b g (Q (a+c))).symm)
end Critical
end Grounds
end
end YM.Contacts.Tempo
