import YM.Contacts.Barrage.Borrow
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}
namespace Reserve
open Origin Slope Ion Resetter Lumen Next.Free Extension.UV.Linear
namespace Oasis
variable (e:Oasis G) {t:ℝ≥0}{i n m r k l q:ℕ}{α:Type}{c b:ℝ}
variable (E:∀ n,RackCore e.a e.M n){X: Field (Fin (r+2)) (Node (Dye G))}
section
abbrev vintage (i n:ℕ):= (e.M.towers n i).A0
abbrev fundHat (e:Oasis G)(k i:ℕ):=1+share e.T G (e.J i) k
lemma fund_pos (k i:ℕ):1 ≤ e.fundHat k i:= le_add_of_nonneg_right (sharing e.T G _ _).le
lemma fair_fund (k:ℕ): e.Fair (e.fundHat k):= (e.fair_const 1 zero_le_one).add (e.fair_z.admits (fun i=> (sharing e.T G _ _).le) ((e.a.fits.deep.eventually_ge_atTop k).mono fun i h=> by
    have hp:=e.a.fits.mono (Nat.le_succ i); exact (e.funded.owns i).preState _ hp k (h.trans hp)))
lemma halo_pay (i): e.haloSpan i ≤ e.κ (i+1) := by
   refine le_trans ((e.halos i).trans (div_le_self (by positivity) (by norm_num))) ?_; have ht:= e.silk i; apply le_trans _ ht; exact le_mul_of_one_le_left (by positivity) one_le_two
lemma reaches (i:ℕ): ((e.haloSpan i):ℝ)/(e.L i).val ≤ e.ξ (i+1):= by unfold haloSpan; push_cast; exact e.lean_in _
lemma amplifies (i n:ℕ)(h:i<n): (nest (e.R i) G (e.vintage i n)).strip (e.haloSpan i) (e.Z i) := by have ht:= e.halo_pay i; exact strip_mono (succeeds (P:=e.R i) (e.bare_a i h) ht (purse_pos ..).le) le_rfl (e.funded.owns i).shelf
private def credit (k r i:ℕ):ℝ:= e.xloose k i * shipped (e.haloSpan i) (e.L i) (Candles G) (Dye G) (r+2) (e.Z i)
private lemma cred (k r:ℕ): e.Fair (e.credit k r):= by
    let p :=e.fair_beam e.fair_z; have hk:e.Fair (fun i=> shipped (e.haloSpan i) (e.L i) (Candles G) (Dye G) (r+2) (e.Z i)):= by exact (e.card_candle.mul p).mul (((e.fair_const _ (Nat.cast_nonneg _)).mul p).pow (r+2-1))
    exact (e.fair_loose k).mul hk
abbrev Bx (k:ℕ)(i:ℕ):= bath (e.ξ i) k (Dye G)
def towerQ (k r i:ℕ)(f g:ℝ): Prop:= ∀ n,i<n→∀ (Y:bore G)(l:ℕ)(c b:ℝ), let r':=r+2; let X:=dazzle Y l r'; 0 ≤ b→ Light Y → softRank (frock r') X → Rooted (e.Bx k (i+1)) X c → (∀ r<r',Rooted (terrain (e.ξ (i+1)) _) (dazzle Y l r) b) → Rooted (e.Bx k i) (lifts (e.atlas E i n) X) ((f /e.fundHat k i)*c+g*b)
private lemma roughGain (k r i:ℕ)(v:ℝ)(hv:0≤v) : ∃ g≥0,towerQ e E k r i g v:= by
   obtain ⟨p,hp,h⟩:= (e.atrDue E).coag; let L:=e.xloose k i * (p i * (p i ^(r+1))); let f:= e.fundHat k i; have hl:0≤L:= by have hy:= (e.fair_loose k).bank i; have hq:=hp.bank i; unfold L; positivity
   have hf:0<f:= zero_lt_one.trans_le (e.fund_pos ..); refine ⟨L*f,mul_nonneg hl hf.le,fun n hn Y l c b hb hy hX hu hP=>?_⟩; let t:=dazzle Y l (r+2); have he:= e.chuting k i (hoist_pay (influx (e.reaches i)) (h i n hn) (hu.weaken bath_terrace le_rfl)); refine he.weaken (fun _=> le_rfl) ((le_of_eq ?_).trans (le_add_of_nonneg_right (mul_nonneg hv hb))); change _= (L*f/f)*c; rw [mul_div_cancel_right₀ _ hf.ne']; unfold L; rw [show r+2-1=r+1 from rfl]; ring
lemma provision_go (i n:ℕ)(h:i<n) : Cabinet (brick G (e.R i) (e.a.clock.kernel.penalty) (e.M.H n (i+1))) (e.provisional E i n):= by unfold provisional; rw [dif_pos h]; exact ((E n).heir i h).governed
private def Mcredit (r:ℕ):ℝ:= drops 1 (r+2) G (fun _=>1) -- unclamped proof
private def coin (r:ℕ):ℝ:= max 0 (Mcredit (G:=G) r)
private lemma coin_payment (r:ℕ)(b:ℝ)(hb:0≤b): drops 1 (r+2) G (fun _=>b) ≤ coin (G:=G) r*b:= by
    refine le_trans (b:=Mcredit (G:=G) r*b) ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) hb); unfold drops Mcredit; unfold drops; simp only [sum_mul, mul_one,mul_assoc]; exact le_rfl -- unfolds Mcredit order
lemma suited (Y: bore G)(h:Cradle (Dye G) Y)(r l:ℕ) : author (extract (dazzle Y l (r+1)))=dazzle Y l (r+1):= by
    apply Spine.relocate; intro x z; unfold dazzle; split; rw [show (fun i:Fin (r+1)=> (z+(x i).1,(x i).2))=(backpack z) ∘ x from funext fun i=> Prod.ext (add_comm ..) rfl]; apply h.here z; rfl
lemma sharp (k r:ℕ)(hk:3 ≤ k): ∀ᶠ i in atTop,towerQ e E k r i ((e.drift i)^2) (e.credit k r i* coin (G:=G) r):= by
   let s:= (r:ℝ)+2; filter_upwards [e.deep_lean (2*s), e.a.fits.deep.eventually_ge_atTop (max (max 5 k) (r+1))] with i hs he
   have hj': e.J i ≤ e.J (i+1):= e.a.fits.mono (Nat.le_succ i); have hj : max (max 5 k) (r+1) ≤ e.J (i+1):= he.trans hj';
   intro n hn Y l c b; intro r' X hb hy hx hu hw;
   let V:=e.R i; let L:=e.L i; let Y':=e.vintage i n; let H:=e.provisional E i n; let A:Cross L (Dye G) (Dye G):= e.atlas E i n; let Z:=coin (G:=G) r; let P:=purse e.T (e.J (i+1)); have hp:= e.ensures E i n hn
   let X' j:= if j=r' then c else b; have hh j (he:j≤r'): Rooted (terrain (e.ξ (i+1)) _) (dazzle Y l j) (X' j):= by unfold X'; split; subst j; exact hu.weaken bath_terrace le_rfl; apply hw; omega
   have hz : lifts A X=lifts (Origin.bleed G Y') X-lifts (nest V G Y') (lottery r' G (dazzle Y l)):= Slope.carpet (t:= e.κ (i+1)) (n:=r+1+1) (e.reaches i) (e.ξ_one (i+1)) (awakened e.lamp hn) (e.provision_go E i n hn) hp.directory (e.z_pos i).le (e.bare_a i hn) (e.halo_pay i) (purse_pos ..).le hp.resource (e.z_pos i).le hy hh
   have hk' : Rooted (e.Bx k i) (lifts (nest V G Y') (lottery r' G (dazzle Y l))) (e.credit k r i*Z*b):= by
      let hZ:Rooted _ _ _:= (lottery_due (n:=r') (e.ξ_one (i+1)) hw); have he:= roof_lift (hZ.weaken (fun _=> le_rfl) (coin_payment r b hb)) (e.z_pos i).le (e.amplifies i n hn) (e.reaches i); convert e.chuting k i he using 1; unfold credit Z r'; rw [show (e.R i).L=e.L i from rfl]; ring -- casts defeq
   change Rooted _ (lifts A X) _ ; rw [hz]
   have hS: ((2*(e.ξ i:ℝ)/(L.val:ℝ))*((↑(r+1):ℝ)+1))≤e.ξ (i+1):= by push_cast; convert hs using 1; unfold s L; ring
   let j:= e.J (i+1); let v:=e.J i; have hi: (censure e.T G j v k (r+1) hk (by omega)).choose ≤ L.val:= by exact (occupied e.T G hk (by omega) (by omega) (by omega) (e.matures i)).trans (e.funded.funds i) -- j opaque
   have hex : e.ξ i ≤ e.flag i:= by apply le_trans _ ((e.halos i).trans (div_le_self (by positivity) (by norm_num))); exact le_mul_of_one_le_left (by positivity) one_le_two;
   have he : (e.ξ i:ℝ)*2≤ e.T.α j:= by rw [mul_comm]; apply le_trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hex) zero_le_two); exact le_trans (by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; exact le_rfl) (NNReal.coe_le_coe.mpr (e.silk i))
   let h' (l:List Axis)(ht:l.length≤3):= e.marched (q:=5) i le_rfl ((by omega):5≤ j) hn l ht; have ha:= (censure e.T G j v k (r+1) hk (by omega)).choose_spec (e.ξ (i+1)) (e.ξ i) L hi (e.a.S.block_odd i) (e.ξ_pos _) he hS X Y' c (suited Y hy.my (r+1) l) (by unfold X dazzle; split; apply hy.my.poem; apply Poem.empty) hx hu h'; rw [show ((↑↑L):ℝ)= ((e.L i).val:ℝ) from rfl, turn_contract, show 1+share e.T G v k=e.fundHat k i from rfl, mul_comm c] at ha; exact ha.sub hk'
-- eventually wage contraction L^-1/2 even *after* salvia budget. early finite arbitrary.
lemma luminous (k r:ℕ)(hk:3 ≤ k) : ∃ f g:ℕ→ℝ, e.Fair f∧e.Fair g ∧ (∀ᶠ i in atTop,f i=(e.drift i)^2)∧ ∀ i,towerQ e E k r i (f i) (g i) := by
   let v(i:ℕ):=e.credit k r i*coin (G:=G) r; obtain ⟨p,hp⟩:= eventually_atTop.mp (e.sharp E k r hk); let T (i:ℕ):= (e.drift i)^2; have hv:e.Fair v:= (e.cred k r).mul (e.fair_const _ (le_max_left ..)); choose f hf hf' using fun i=> e.roughGain E k r i (v i) (hv.bank i)
   let w i:= if p ≤ i then T i else f i; have he:∀ᶠ i in atTop,w i=T i:= (eventually_ge_atTop p).mono fun i hi=>if_pos hi; refine ⟨w,v, (e.fair_const 1 zero_le_one).admits ?_ (he.mono fun i hi=>?_ ),hv, he,fun i=>?_⟩
   · intro i; unfold w; split; exact sq_nonneg _; exact hf i
   · rw [hi]; exact pow_le_one₀ (e.drift_pos _).le (inv_le_one_of_one_le₀ (e.turn_ge _))
   · unfold w; split; next h=> exact hp i h
     next h=> exact hf' i
end
end Oasis
end Reserve
end
end YM.Contacts.Barrage
