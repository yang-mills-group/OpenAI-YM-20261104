import YM.FVA2.CapLattice
/-!
# Rank cap $≤ grade+n$ implementing ℏ selection on log-rescaled sources.

`BookM` high solver extended use (not another assumption).
Use *same* all-orders parameters then identify physical fields exactly under sym/normalization. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Reed.Wax
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Local.Physical
open Mach Train Pearl Emit Wind Wind.Leading Menus Program Knobs Native.Paint Native.Wilsonian Tone Momentum City Logarithm
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{m n h d:ℕ}{p:Team}{B:Deck G} {i j:ℤ}(y:ℝ)
variable (t: Glyph B d)(W:BookM B)(p:Team)
private abbrev Κn (t:Glyph B d)(n:ℕ):= { S:Tact B d // (n=0→FitOrder t S) ∧ credit t n S }
private def cord (P:Code (Κn t)) (i:ℕ): Tact B d:=( P i ).val
private def race : Knobs (Κn t) G where
    wake P:= ( SeekM W p d ).wake (cord t P)
    stay _ _ _ h:=(SeekM W p d).stay _ _ _ (fun i hi=>congr_arg Subtype.val (h i hi))
private lemma erasePage {he:ℕ} (Q:Code (Κn t))(X:Recount G)(hT:∀ x,Limit (X n x) ((t.grade:ℤ)+n))(hv:t.grade+n < he)(hx:i≤d)(u:Recount G)(hs:Disc false 0 u X 1 d) : High.slice ((race t W p).wake Q n-X n) false he i y=0:= by
    let Y:=horizonM W p ( cord t Q ); let L:Recount G:=col Y; apply excuse (F:=L) ?_ ?_ ?_ hx y
    · intro x w h k hk; rw [torch_piece w h (L n x), torch_piece w h (X n x), maskOff (u:=t.grade+n) (by omega) ( show Limit ( L n x ) _ from horizon_t x.1 W p (cord t Q) t ( fun n=> ( Q n ).property.2 ) n ( exp x.2 ) ), maskOff ( by omega : (t.grade:ℤ)+n < he ) (hT x) ] -- ambiguity `shift`
    · exact fun x w=> (aquaM W p (cord t Q)|>.owes n|>.stay x.1).joint.routine _ _
    exact fun x w=> (hs.master.road ℝ (ray w) n (Nat.zero_le _) (fun v=> Bool.noConfusion v) (fun v=> Bool.noConfusion v)).1 x
-- Need subtype default inhabitant 
private def νκ (t:Glyph B d): Code (Κn t):= fun i=> ⟨ (script t i).1,(script t i).2,(by refine ⟨fun j hj=>?_,fun s x _=> rfl⟩; change (if j=t then 1 else 0)=_; rw [if_neg (fun h=>?_)]; subst j; omega )⟩
theorem headLock (A: Recount G)(X:Recount G)(h:G.Simple)(hq:Fixed (col (skyline G p)) A true 4 1) (hh: Disc false 0 A X 1 d)(hx: PhysicalHF t X)(HV:∀ n x,Limit (X n x) ((t.grade:ℤ)+n)): ∃ F: Acts B d, FitOrder t (F 0) ∧ Fixed (col (horizonM W p F)) X false d 0 ∧ ∀ n,credit t n ( F n ):= by
   let K:= race t W p; let V0:= col (skyline G p); let W':=mark_seekM W (p:=p) (d:=d) h;
   have HT (Q:Code (Κn t)): Spheres wave (spaceL G) V0 (K.wake Q) 1 0 false:= W'.law _;
   suffices he : ∃ P: Code (Κn t), Fixed (K.wake P) X false d 0 by obtain ⟨P,hP⟩:=he; exact ⟨ cord t P, (P 0).property.1 rfl,hP,fun i=> (P i).property.2 ⟩
   refine assigned (B:=fun _=> V0) HT hh.master hh.good (fun i=>W'.occurs (cord t i)) hh.open' ?_ (by omega) ?_ (νκ t)
   · intro C n hn hp i hi r; exact hq (n-i) (by obtain he:=path_in hi; omega) _ (fun _ => Nat.succ_pos r)
   intro n hn r hr u hu hv C EE HE
   let M:= K.wake C n-X n; let J:= slice M false r u; have hz:= advanced (HT C) hh.master hn hr EE
   by_cases hk: n=0 ∧ t.grade≤ r; · obtain ⟨rfl,H⟩:=hk; refine ⟨C, Move.refl J ?_ ⟩; intro i w _ hx'; change slice _ _ _ _ _ _=_; exact congr_fun (guardedM W p (P:=cord t C) ((C 0).property.1 rfl) hx H hv hh i) w
   by_cases hL:t.grade+n < r; · refine ⟨ C,Move.refl J ?_⟩; intro i w _ hx'; exact congr_fun (erasePage i t W p C X ( HV n ) hL hv A hh) w
   have ht : Ready J:= slice_ready hz hv (Ready.sub ((HT C).poly n) (hh.master.poly n));
   have hu' (i:ℝ) : J i∈ Lease G u r 0:= lease_one.mpr ⟨slice_solid hz hv fun t=> ((HT C).trueC n t).sub (hh.master.trueC n t),slice_form hz hv,rank_slice⟩
   have ht (i:ℝ) : natQ (J i)=0:= funext (fun l=> closes (HT C) hh.master hh.good hn hr EE hv HE i l (fun v=>Bool.noConfusion v))
   obtain ⟨a,g,h0,h1,hJ,hI,ho⟩:= mark_inter (show Ready J from (by assumption)) hu' ht B; obtain ⟨Q,T,hQ,hT,hW⟩:= Menus.room_hereM (n:=n) W p (cord t C) hu hv h0 h1 hJ hI
   let P := Menus.patch (cord t C) Q T n; have he' : FitOrder t (P 0):= fix_order (P:=cord t C) (( C 0 ).property.1 rfl) hQ hT.le (by omega)
   have hq' (i:ℕ): credit t i ( P i ):= by
       rcases eq_or_ne i n with hi|hi; swap; · unfold P; rw [ Menus.patch_bef _ _ _ hi ]; exact ( C i ).property.2 -- rw let f?
       subst i; unfold P Menus.patch; simp only [if_true]; refine ⟨fun i hi=> ?_,fun i=> Limit.sub (( C n).property.2.2 i) (( T.ranks i ).up (by omega))⟩;
       change (C n).val.register i-Q i=_; rw [ (C n).property.2.1 i hi, show Q i=0 from Classical.byContradiction (fun h=>?_), sub_zero ]; obtain hp:= hQ.grade i h; omega
   let Y:Code (Κn t):= fun i=> ⟨P i,fun h=> h ▸ he',hq' i⟩;
   have hm : ∀ i<n,(C i)=(Y i):= fun i hi=> Subtype.ext (hW.past i hi)
   refine ⟨Y, Move.replace (rewind (K:=K) rfl rfl hm (fun i=> (((aquaM W p (cord t C)).owes n).stay i).joint) (fun i=> (((aquaM W p P).owes n).stay i).joint) (mark_payM W hW)) (fun i w hw hI=> congr_fun (congr_fun ho i) w)⟩
end YM.MS.Reed.Wax
