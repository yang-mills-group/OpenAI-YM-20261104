import YM.Frontier6.Multi.Capture.Sampling

/-! Scene threading across cell seams via root anchors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies.Doors
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Matrix
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Next.Rank Next.Rank.Station Cells
open Ribbons
open scoped Topology BigOperators Classical
variable {G:Gauge}{O:Type}[DecidableEq O][Fintype O]
variable (C:Family G)(J j p:ℕ)
variable (L : O → Site (C.side j p))
set_option quotPrecheck false
local notation "Q"=> hands C p J
local notation "V"=> Site (C.side J p)
local notation "E"=> Mix.camp C p J

local notation "Y"=> placements C J j p L
variable {δ φ ψ ζ:ℕ→ℝ}{u:ℕ→ℕ→ℝ} {W:Bid.Worth}{r:ℕ→ℕ}{D:∀ N p i,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (h:Scrim C W ζ ψ φ δ u r D) {χ:ℕ→ℝ}{d:ℕ}{ε:ℝ}
variable (h' : WaresAll C (δ:=δ) (r:=r) (μ:=D) (C.ref d) d χ δ (PhysicalNext.Repeat.Legato.bling C.path.levels)) {N m k i:ℕ}
variable (w:O→ℝ) (F:O→ Config G (C.side N p)→ℂ)(hi:∀ i,Continuous (F i))
local notation "T"=> center C.S p
local notation "Z"=> Now (Site (C.side J p)) O

local notation "f'"=> allCopy C J p F
-- Lean param order inspect
local notation "P'"=> C.path.levels.budget
local notation "R"=> C.path.rep N p
local notation "X"=> PhysicalNext.Repeat.Legato.bling C.path.levels m
variable (hM:C.Makes)(hR:Created C)(root:O)
local notation "T'"=> Equiv.swap (0 : V)
local notation "Φ"=> C.path
local notation "τ"=> fun hN:J ≤ N=> birth Z (C.path.rep N p N) (f' hN)
lemma spun (hN:J ≤ N) (root:O) : (droplet («V»:=V) root).reap ∘ birth Z (R N) (f' hN)=birth (Bud V) (R N) (fun i:Site (C.side J p)=> (center C.S p hN 0).copy i (∏ i,F i)):=by
   rw [Concentrate.expander]; refine congr_arg (birth (Bud V) (R N)) (funext fun i=>funext fun x=>?_)
   rw [totalCopy]; have hz: (droplet root).fiber i= univ.image (fun j=>(i,j)):= by ext ⟨a,b⟩; simp [Concentrate.fiber,droplet,eq_comm]
   rw [hz,prod_image]; exact (show Injective (fun j:O=>(i,j)) from fun j k h=> congr_arg Prod.snd h).injOn
-- permits required financing; outputs true chamber
include hi h h' hM hR root
open Relay Exponential Bid
local notation "n"=> Fintype.card O
lemma stamp (hm:J ≤ m)(hj:m+1 < j)(hN:j < N)(hg:Stock.Tabs (C.path.levels))(hx : Stock.Tabs.opens C.path.levels 1 J k)
   (hk:k ≤ m)(hk':C.ref d ≤ k)(tt:O→ℕ)(q:(i:O)→ C.label (tt i))(B:O→ℝ)
   (hG:Travel C.path δ r D χ 0 (Q) T' E (placements C J j p L) m j (C.ref d) ε N) (hs:∀ i:O,loops C j p (L i) (m+1)=0) (hV: Pairwise (fun i y=> (C.path.levels.budget j).B^2 ≤ separation (L i) (L y))) -- fix shadow
   (hB:∀ i,0<B i)(ht:∀ i,C.ref (tt i)≤j)(hP:∀ i,B i*Next.Rank.Spindle.paid C (tt i) j N p (q i)≤ u (tt i) j)
   (he:∀ i:O,F i= C.O N p (q i) (placements C J j p L N (0,i))) (hw:∀ i, w i=δ j*(φ j* B i)/8)(ha:∀ i, Interior ((center C.S p (hm.trans (m.le_succ.trans (hj.le.trans hN.le))) 0).chamber 0) (F i))(hc:∀ z:C.label d, Interior ((center C.S p (hm.trans (m.le_succ.trans (hj.le.trans hN.le))) 0).chamber 0) (C.O N p z 0)) (hu:GridApprox.room C.path.levels J m (lensScope C d))
   (w0 e b:ℝ)(hh:0<w0)(hb:0 < b)(hW:w0 ≤ warrant C.S ε ((Fintype.card O)+1) (n) j (m+1) (total w))
   (hE: 4*(1+(Φ|>.levels.params m).columns)*(2*(C.S.a (m+1)^d*(X*(1/(2*w0)))))≤ e)
   (hp: march (fun _:Unit=>b) φ k m () ≤ δ m*(w0/(16*X))) (hC:32*(1+(Φ|>.levels.params m).columns)*b*‖alto C.path k d‖*(e/gainChart C.path m k) ≤ u d k/2) :
    ∃ z:C.label d,Next.UVStress.quota C d m N p z ≤ 2*e ∧ (center C.S p (hm.trans (m.le_succ.trans (hj.le.trans hN.le))) 0).rootTest (C.beta N p) ((∏ i,F i)-C.O N p z 0) ≤ 2*(stakes C J k/b):=by
    obtain ⟨σ,hT⟩:= h'.city; have hL:=hj.trans hN; have hmN:m<N:=m.lt_succ_self.trans hL; let hJN:= hm.trans hmN.le; let Φ':= f' hJN; let Y':= τ hJN
    have hU:Integrable Y' (prior G _):=(hatCont C N p Φ' (fun i=> show Continuous (Φ' i) from cappedC C J p N hJN (fun _=>F i.snd) (i.1,true) (hi i.snd)) (show Continuous (R N|>.eval) by rw [(hM.wilson.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hf:= prepared C J j p L h h' w F hM root hm hj hN tt q B hT hG hU (summit C J j p L (by omega) hV) hB ht hP he hw
    have ht' (i):0 < w i:= by rw [hw];exact div_pos (mul_pos (h'.funs j (by omega)).1 (mul_pos (h.costs.stay.water j (Nat.zero_le _)|>.1) (hB i))) (by norm_num)
    have hv:= herd C J j p L (hm.trans m.le_succ) hj.le hs
    have y:= walking C.path δ r D σ χ 0 Q T' E Y hM.wilson (C.ref d) hT w0 Y' root ε hG hj hN (fun i=> by rw [hv _,hv _]; simp) hh hW (total_pos ht'|>.le) hU hf
    let t:= (C.S.a (m+1)^d*(X*(1/(2*w0)))); let Z':= march (fun _:V=>b) φ k m; let W:= (droplet («V»:=V) root).reap ∘ gust Φ N p N Y' m hmN.le
    have hi'(v:V): Z' v = march (fun _:Unit=>b) φ k m ():=by
       suffices h:∀ j:ℕ,march (fun _:Site (C.side J p)=>b) φ k j v=march (fun _:Unit=>b) φ k j () by exact h m
       intro j; induction j with
       | zero=>rfl
       | succ j ih=> by_cases hv:k ≤ j <;> simp [march,hv,ih]
    have hO(i : ℕ)(he:J ≤ i):Occupancy (E i) (r m):= fun a=> (Occupancy.of_injective (show Injective (E i) by rw [show E i=(C.S.toDepth he p).embed from funext fun j=> elev C J p i he j]; exact (C.S.toDepth he p).embed_injective) a).trans (h.back _)
    obtain ⟨z,hKt,hS,h₁,h₂⟩:= Created.bridge C N p d m Q (E m) Z' W hR (supplied C.path δ r D σ χ 0 Q E Y hM.wilson (C.ref d) hT w0 Y' root d hmN (hk'.trans hk) hU y (funext (fun x=> hv (x,root))) (zeroMama C J p m hm) (hG.back m le_rfl (by omega)) (P_on C J p) (hO _ (hm.trans m.le_succ)) (hO _ hm) X Z' (h'.brings m (by omega) N p hmN |>.2) hh (h'.dollars m (by omega)) (march_pos C.path k δ φ (fun _:V=>b) (fun _=>hb) (allBrine C h k) _ hk) (fun i=> (hi' i).le.trans hp))
    have ht:0 < t:=by unfold t;exact mul_pos (pow_pos (C.S.a_pos _) _) (mul_pos (lt_of_lt_of_le zero_lt_one (h'.dollars _ (by omega))) (by positivity));
    apply bequeathed C N m k p d hM b h hg J hx (∏ i,F i) z hk' (hk:=hk) hmN hu hc (by rw [show (∏ i,F i)=fun x=>∏ i,F i x from (by ext; simp)]; fun_prop) (by
       have hX:(∏ i,F i)=fun x=>∏ i,F i x:=by ext; simp
       rw [hX]; exact Interior.combines F univ fun i _=>ha i) hKt hS (by linarith only [h₁]) (mul_pos zero_lt_two ht) hE hb hC
    have hz:= (droplet («V»:=V) root).gust_from _ hU hmN.le; unfold W at h₂; rw [← hz] at h₂; unfold Y' at h₂; rw [spun] at h₂; exact h₂
end YM.MergeProof.Canopies.Doors
