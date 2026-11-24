import YM.FormalBulk08.North.Pied

/-! Crest limits. Allow pad by zero or use unpadded §kbulk limiting family. Communicate through finite E. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.North
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I J:Type}{G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{E e r m:ℕ}{W:Lab G K I}
variable (a:hue G)(x:Leaf W.scrolls)(ρ)
def camp (T:Pot G): OrbitV (Biglot (BoardL G (W.pat x) (W.wood x.a x.b))):=fun e r=> if e=0 then 0 else pearl (lands (limY x)) (ouzo T ρ _ _ K e r)
def obs (T:Pot G): Pot G:= fun e r=> ∑ i∈Finset.range (3*e+1),jetty (coastRight _ _ _) (swim (lands (limG x)) (camp ρ x T) i e r)
def crest (T:Pot G): Pot G:= fun e r=> if e=0 then (heir a ρ W x.a x.b) e r else if r=0 then 0 else obs ρ x T e r
-- fixed positive E observation
abbrev nations (x:Leaf W.scrolls) (n:ℕ):= saga ρ a W x.a (seqN x n) (x.b+1)
variable {ρ}
lemma blizzard {T: Pot G}(hv:Vivid T)(hp:LocalRatio ρ):Fiery (camp ρ x T):= by
   intro e r he; unfold camp at he;split at he
   · contradiction
   rename_i hz; by_contra! hh; have hx:T e r=0:=by by_contra hV;have hp:=hv.valence _ _ hV;omega
   have hv := WO_vanish G ρ hp (W.wood x.a x.b) e r (Or.inl (show e≠r by omega)); unfold ouzo Bank.atlas altitude at he; rw [hv,TO_vanish _ _ _ _ _ (by omega),hx,jetty_zero,pearl_zero,sub_zero,pearl_zero,zero_add,pearl_zero] at he; contradiction
variable (hp:Use W ρ E)(h: LocalRatio ρ)(hs:G.Simple)
include hp h hs
lemma stellar (he:e≤ E)(z:Fin r):
     let V:=fun i=> destination (W.V x.a) (seqN x i) x.b
     let U:= W.wood x.a x.b
     let M:= heir a ρ W x.a (x.b+1)
     let A:= nations ρ a x
     Totem staticT (fun _=>fame (BoardL G (W.pat x) U)) (fun _=>W.windowD x) (coinR x) (fun i=>cola (A i) ρ (V i) U K e r) (fun _=>camp ρ x (stopper M E) e r) := by
    intro V U M A; unfold cola camp; by_cases he':e=0
    · simp only [he', ↓reduceIte];apply Aster.voids
    simp only [he',↓reduceIte]; have hy i:= coinP x i; let s:= W.windowD x; have h' (_:ℕ):0≤s:=(hp.zero x).le
    apply pearl_delta (soft_coin _ (Fintype.card (BoardL G (W.pat x) U))) (soft_coin _ (Fintype.card _)) h' z (meet_land x hp) hy
    have he': (stopper M E) e=M e:= if_pos he; let Y:=WO (W.pat x) U ρ e r; obtain ⟨C,c⟩:= WO_bail G e r s (P:=W.pat x) U ρ
    have hx:Cost staticT (fun _=> fame _) (fun _=> s) (fun _=>Y):= ⟨_,soft_coin _ C,fun _=>c⟩
    refine Totem.plus ?_ (Totem.constant hx); let Q:=TO G (W.pat x) K e r; let S:=pane G (W.pat x) U; have hp':ease (V:=fun _=>Board G (W.pat x)) staticT (fun _=>s) (fun _=>S):= ⟨_,soft_coin _ 1,fun _=>zero_le_one,fun _=> pane_pay _ _⟩
    apply pearl_delta (V:=fun _=>Board G (W.pat x)) (soft_coin _ _) (soft_coin _ _) h' z (maori_constant hp') hy
    obtain ⟨B,b⟩:= TO_bail G e r s (W.pat x) K; refine Totem.minus ?_ (Totem.constant (show Cost staticT (fun _=> fame _) (fun _=>s) (fun _=>Q) from ⟨_,soft_coin _ B,fun _=>b⟩)); let R:=winging (Rim G (W.pat x)) (Loc G 1); have hv:ease (V:=fun _=> Rim G (W.pat x)) staticT (fun _=>s) (fun _=>R):= ⟨_,soft_coin _ 1,fun _=>zero_le_one,fun _=> wing_strip _⟩
    apply pearl_delta (soft_coin _ (Fintype.card (Rim G (W.pat x)))) (soft_coin _ _) h' z (maori_constant hv) hy
    have hh: Totem staticT (fun _=> fame _) (fun _=> W.windowU x) (coinR x) (fun i=> A i e r) (fun _=>stopper M E e r) := by rw [he'];exact totem_hold a hp h hs (porch x) he
    let L:= (W.pat x).L; have ht:= (W.turn_whose hp x).ship
    obtain ⟨⟨C,c,Y⟩,⟨B,b,H⟩,D,d,K1,U1⟩:=hh
    have hS:=soft_coin staticT (Real.exp (8*s)); refine ⟨⟨_,hS.times c,fun i=> packet_bill L ht (hp.zero x).le (Y i)⟩,⟨_,hS.times b,fun i=>packet_bill L ht (hp.zero x).le (H i)⟩,_, hS.times d,fun i=>mul_nonneg (Real.exp_pos _).le (K1 i),fun i=>?_⟩; rw [mul_assoc]; exact packet_bill L ht (hp.zero x).le (U1 i)
omit hp h hs in
lemma camps (T S:Pot G)(h:∀ i≤e,T i=S i): obs ρ x T e r=obs ρ x S e r := by
    unfold obs; refine Finset.sum_congr rfl fun i _=> ?_; have hh j (hz:j≤e): camp ρ x T j=camp ρ x S j:= by funext r; simp [camp,ouzo,Bank.atlas,altitude,h j hz]
    rw [through_swim _ _ _ i e hh e le_rfl]

lemma born : Vivid (stopper (heir a ρ W x.a x.b) E):= by
   exact boundP ((eventually_ge_atTop x.b).mono fun N hN=> (show Vivid (saga ρ a W x.a N x.b) from (genu (W.V x.a) (W.wood x.a) (W.toEmpire.bill x.a) ρ a h hs hN).toVivid)) (fun e he r=> North.crown a hp h hs he r x)
lemma summits (he:e≤E)(hy:0<e)(z:Fin r):
    let K1:= fun i=> eating ρ a W (fun _=>seqN x i) x.a x.b
    let V:=crest ρ a x (heir a ρ W x.a (x.b+1))
    Totem staticT (fun _=> fame _) (fun _=> W.windowD x) (coinR x) (fun n=> K1 n e r) (fun _=> V e r):= by
    intro Q V; let F:=fun i=> destination (W.V x.a) (seqN x i) x.b; let U:=W.wood x.a x.b; let M:= heir a ρ W x.a (x.b+1); let Z:= stopper M E;let T:= nations ρ a x
    have hv: Vivid Z:=born a (porch x) hp h hs; have hr:0<r:= by have :=z.isLt;omega
    have hr': Fiery (camp ρ x Z):= blizzard x hv h; have ht i: Fiery (cola (T i) ρ (F i) U K):= fairy (T i) ρ (F i) U K (genu (W.V x.a) (W.wood x.a) (W.toEmpire.bill x.a) _ a h hs (N:=seqN x i) (i:=x.b+1) (by unfold seqN;omega)).toVivid h
    rw [show V e r=obs ρ x Z e r from (by change crest _ _ _ M _ _ = _; rw [crest,if_neg (by omega),if_neg (by omega)];exact (camps (ρ:=ρ) x Z M (fun j hj=>if_pos (hj.trans he))).symm)]
    simp only [Q,eating,waken,if_neg (show ¬ e=0 by omega),if_neg (show r≠0 by omega),coastRun,obs]; apply totem_sums _; intro i hi; have hZ (_:ℕ):0≤W.windowD x:=(hp.zero x).le
    have hh : Totem staticT (fun _=> fame (BoardL G (W.pat x) U)) (fun _=> W.windowD x) (coinR x) (fun n=> swim (lands (booket x n)) (cola (T n) ρ (F n) U K) i e r) (fun _=> swim (lands (limG x)) (camp ρ x Z) i e r):= by
        apply fares_hop (e:=E) (r:=0) hZ ht (graspG x hp) (fun _=>hr') _ _ _ _ ?_ hr
        · intro b s q hz hV ht; exact stellar a x hp h hs (by unfold precede at ht;omega) ⟨0,q⟩
        · apply Or.inl; unfold precede;omega
    exact Totem.shore hh hZ
end YM.FormalBulk08.North
