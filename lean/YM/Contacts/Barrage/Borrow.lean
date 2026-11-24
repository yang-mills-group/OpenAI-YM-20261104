import YM.Contacts.Barrage.Bounty
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
open Balance Oasis
variable (e:Oasis G) (E:∀ n,RackCore e.a e.M n) {H:ℕ→ℕ→Prop}{k i n:ℕ}
abbrev Wd (i:ℕ): Type:= Mixed G (e.R i)
abbrev line (i n) := axisLine G (e.R i) (prom (e.provisional E i n))
abbrev out (i n) := axisSky G (e.R i) (e.atlas E i n)
lemma cardHeight : e.Fair (fun i=> Fintype.card (e.Wd i)):= e.fair_z.admits (fun i=> by positivity) (Eventually.of_forall fun i=> (e.funded.owns i).bud.2.2)
lemma card_pre : e.Fair (fun i=> Fintype.card (Cellar G (e.L i))) := e.fair_z.admits (fun _=> by positivity) (Eventually.of_forall fun i=>(e.funded.owns i).bud.1)
lemma card_candle : e.Fair (fun i=> Fintype.card (Co (e.L i) (Candles G))) := e.fair_z.admits (fun _=> by positivity) (Eventually.of_forall fun i=> (e.funded.owns i).bud.2.1)
def pier (α:ℕ→Type) := fun i=> terrain (e.haloSpan i) (α i)
lemma line_due (i:ℕ)(h:i<n): (e.line E i n).strip (e.haloSpan i) (e.Z i):= line_shape (brace _ (e.ensures E i n h).directory (e.z_pos i).le) (e.z_pos i).le
lemma racket : Reef e Nat.lt (e.pier e.Wd) (fun i n=> plane (e.line E i n)):= by
   obtain ⟨f,hf,h⟩:= e.buys E; refine ⟨⟨_, e.cardHeight.mul e.fair_z, fun i n ht=> ?_⟩,_,e.cardHeight.mul hf,fun i n m hn hm =>?_⟩
   · let hp:= flight_stem (e.line_due E i (n:=n) ht) (e.z_pos i).le; exact ⟨hp.left,hp.rows,hp.columns⟩
   have ht:= (h i n m hn hm).directory; let v:=f i*e.η i (min n m); have hv: 0≤v:= mul_nonneg (hf.bank i) (e.η_pos ..).le; let S:= e.provisional E; have he: minusRows (e.line E i n) (e.line E i m)=axisLine G (e.R i) (prom (minusRows (S i n) (S i m))):= by rw [← prom_diff (P:= e.R i)]; ext (a|a) (x|x) z<;> first| rfl |simp [line,axisLine,minusRows]
   let T:= e.Wd i; rw [mul_assoc (Fintype.card T:ℝ)]; change Pulse.Track _ (plane (minusRows _ _)) _ ; rw [he]; have hh:= flight_stem (line_shape (S:=e.R i) (brace (minusRows (S i n) (S i m)) ht hv) hv) hv; exact ⟨hh.left,hh.rows,hh.columns⟩
lemma shine_due (i:ℕ)(h:i<n): (e.out E i n).strip (e.haloSpan i) (1+e.Z i):= sky_shape (U:= e.atlas E i n) (e.ensures E i n h).resource (e.z_pos i).le
lemma shines : Loans e Nat.lt (fun i=> tunnel (α:=e.Wd i) (β:=Dye G) (e.haloSpan i)) (fun i n=> plane (e.out E i n)):= by
   obtain ⟨f,hf,h⟩:= e.buys E; let a(i:ℕ):ℝ:= Fintype.card (Dye G); let p i:=1+e.Z i; let c i:ℝ:=Fintype.card (e.Wd i)
   let hp:= (e.fair_const 1 zero_le_one).add e.fair_z; have hv:e.Fair a:= e.fair_const _ (Nat.cast_nonneg _); have hk:e.Fair c:= e.cardHeight; refine ⟨⟨_,(hk.add hv).mul hp,fun i n h=> ?_⟩,_,(hk.add hv).mul hf,fun i n m hn hm=>?_⟩
   · exact weir_up (flight_stem (e.shine_due E i h) (hp.bank i)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hv.bank i)) (hp.bank i)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hk.bank i)) (hp.bank i))
   let z:=f i*e.η i (min n m); have hx:= (h i n m hn hm).resource; have hz: 0≤ z:= mul_nonneg (hf.bank i) (e.η_pos ..).le; let W n:=e.out E i n; let b:= minusRows (W n) (W m); have he:b.strip (e.haloSpan i) z:= by
     rintro (a|a) j; · simp [Width,b,W,out,axisSky,minusRows]; exact budget_loosen budget_zero hz
     exact hx a j
   let u:=e.η i (min n m); change Weirs _ (plane b) ((_ *f i)*u) ((_ *f i)*u); rw [mul_assoc]; exact weir_up (flight_stem he hz) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hv.bank i)) hz) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hk.bank i)) hz)
section cross
variable {α β:ℕ→Type} [∀ i,Fintype (α i)][∀ i,Fintype (β i)] {f:ℕ→ℝ} {R:∀ i,Cross (e.L i) (α i) (β i)}
lemma fair_beam (hp:e.Fair f): e.Fair (fun i=> beamPrice (e.haloSpan i) (f i)):= ((e.fair_const (Real.exp 2) (Real.exp_pos _).le).mul hp).admits (fun i=> mul_nonneg ((Real.exp_pos _).le) (hp.bank i)) (Eventually.of_forall fun i=> by apply mul_le_mul_of_nonneg_right _ (hp.bank i); apply Real.exp_le_exp.mpr; linarith only [show (e.haloSpan i:ℝ)≤1 from NNReal.coe_le_coe.mpr (e.tent i)])
abbrev plume (α β:ℕ→Type)(i:ℕ):= access (e.L i) (e.haloSpan i) (α:=α i) (β:=β i)
lemma skewer (h:e.Fair f)(hp:∀ i, (R i).strip (e.haloSpan i) (f i)) (ha:e.Fair (fun i=> Fintype.card (Co (e.L i) (α i))))(hb:e.Fair (fun i=>Fintype.card (β i))): e.Permit (fun i b=>Weirs (e.plume α β i) (install (R i)) b b):= by
    let p:= e.fair_beam h; refine ⟨_,(ha.add hb).mul p,fun i=>?_⟩; exact weir_up (ledgers (hp i) (h.bank i)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hb.bank _)) (p.bank i)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (ha.bank _)) (p.bank i))
lemma fixedCross (h:e.Fair f)(hp:∀ i,(R i).strip (e.haloSpan i) (f i))(ha:e.Fair (fun i=> Fintype.card (Co (e.L i) (α i))))(hb:e.Fair (fun i=> Fintype.card (β i))): Loans e H (e.plume α β) (fun i _=> install (R i)):= by
   obtain ⟨p,hp,hq⟩:= e.skewer h hp ha hb; refine ⟨⟨p,hp,fun i n _=> hq i⟩,_,e.fair_const 0 le_rfl,fun i n m _ _=>?_⟩; simp only [sub_self, zero_mul]; exact ⟨le_rfl,le_rfl,by intro i; simpa using budget_zero,by intro i; simpa using budget_zero⟩
end cross
lemma adoptDue : Loans e Nat.lt (e.plume (fun _=>Dye G) e.Wd) (fun i n=> install (adopt (Cellar G (e.L i)) (Dye G))):= e.fixedCross (R:=fun i : ℕ=> adopt (Cellar G (e.L i)) (Dye G)) (e.fair_const 1 zero_le_one) (fun i=> adopt_cost _ _ _) e.card_pre e.cardHeight
lemma atrDue : Loans e Nat.lt (e.plume (fun _=> Dye G) (fun _=> Dye G)) (fun i n=>install (e.atlas E i n)):= by
   obtain ⟨f,hf,h⟩:= e.buys E; let a(i:ℕ):ℝ:= Fintype.card (Dye G); let g(i:ℕ):ℝ:= Fintype.card (Cellar G (e.L i)); have ha:e.Fair a:=e.fair_const _ (Nat.cast_nonneg _); have hh:e.Fair g:= e.card_pre
   let hp:= e.fair_beam e.fair_z; let hx:= e.fair_beam hf; refine ⟨⟨_,(ha.add hh).mul hp,fun i n hn=> weir_up (ledgers (e.ensures E i n hn).resource (e.z_pos i).le) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (ha.bank i)) (hp.bank i)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hh.bank i)) (hp.bank i))⟩,_, (ha.add hh).mul hx, fun i n m hn hm=>?_⟩
   let z:=e.η i (min n m); let y:=beamPrice (e.haloSpan i) (f i); let t:=beamPrice (e.haloSpan i) (f i*z); let s:=(a i+g i)*t; have hz:0≤f i*z:= mul_nonneg (hf.bank _) ((e.η_pos ..).le); have ht:0≤ t:= mul_nonneg (Real.exp_pos _).le hz; have he:(a i+g i)*y*z=s:= by unfold s y t beamPrice; ring
   dsimp only; rw [he]; exact weir_up (ledgers (L:=e.L i) (α:=Dye G) (β:=Dye G) (h i n m hn hm|>.resource) hz) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (ha.bank i)) ht) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hh.bank i)) ht)
section chute
variable {ι X:Type} [Fintype ι] {F:Field ι (Node X)}{b:ℝ}
abbrev xloose (e:Oasis G)(k:ℕ)(i:ℕ):ℝ:= k.factorial * e.Z i ^k * Real.exp 1
lemma fair_loose (k:ℕ): e.Fair (e.xloose k) := ((e.fair_const _ (Nat.cast_nonneg _)).mul (e.fair_z.pow k)).mul (e.fair_const _ (Real.exp_pos _).le)
lemma chuting (k:ℕ)(i:ℕ)(h:Rooted (terrain (e.haloSpan i) X) F b) : Rooted (bath (e.ξ i) k X) F (e.xloose k i * b):= by
   let Q:=e.Z i; let W:= (e.ξ i:ℝ); let U:=Real.exp 1; let t:ℝ:=k.factorial; let v:=e.xloose k i
   have ht (r:ℝ)(hr:0≤r) : Real.exp (W*r)*(1+r)^k ≤ v*Real.exp ( (e.haloSpan i:ℝ)*r) := by
      have hu:W≤1:= NNReal.coe_le_coe.mpr (e.ξ_one _); have hp:0<W:= NNReal.coe_pos.mpr (e.ξ_pos _); have hf: 0<t:=by unfold t; positivity
      have hy:Q*W=1:= mul_inv_cancel₀ (e.z_pos i).ne'; have hz : 0 ≤ Q:= (e.z_pos i).le
      let A:=1+r; have hN:= Real.pow_div_factorial_le_exp (W*A) (mul_nonneg hp.le (add_nonneg zero_le_one hr)) k
      have he : Real.exp (W*A) ≤ U*Real.exp (W*r):= by unfold A; rw [mul_add,mul_one, Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu) (Real.exp_pos _).le
      calc
        _=Real.exp (W*r)* (Q^k * (W*A)^k):= by rw [←mul_pow, ← mul_assoc Q W A,hy,one_mul]
        _ ≤ Real.exp (W*r)*(Q^k*(U*Real.exp (W*r)*t)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ( (div_le_iff₀ hf).1 (hN.trans he)) (pow_nonneg hz _)) (Real.exp_pos _).le
        _ = _:= by rw [show (e.haloSpan i:ℝ)* r=W*r+W*r from (by unfold W haloSpan; push_cast; ring),Real.exp_add]; unfold v xloose t Q U; ring
   have hv: 0≤v:= (e.fair_loose k).bank _; let m:=terrain (e.haloSpan i) X; let l:=bath (e.ξ i) k X; have hs (x:ι→Node X): l.bill x ≤ v*m.bill x:= by
      have hb : 1≤ v:= by simpa using ht 0 le_rfl
      apply l.wide x (one_le_mul_of_one_le_of_one_le hb (m.one_bill _)); intro i j; exact (ht _ (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_left (m.width x i j) hv)
   refine ⟨mul_nonneg hv h.cash,fun i x=> ?_⟩; exact budget_mono (budget_scale hv (h.row i x)) (fun _=>by positivity) (fun p=> (mul_le_mul_of_nonneg_left (hs p.val) (norm_nonneg _)).trans_eq (mul_left_comm ..))
abbrev jetBath (k:ℕ)(α:ℕ→Type) := fun i=> bath (e.ξ i) k (α i)
abbrev facet (α:ℕ→Type) := fun i=> terrain (e.ξ i) (α i)
variable {γ:ℕ→Type}{u:∀ i,ℕ→Field ι (Node (γ i))}
lemma removed (k:ℕ)(h:Balance.Stable e H (e.pier γ) u): Balance.Stable e H (e.jetBath k γ) u:= by obtain ⟨⟨p,hp,hq⟩,q,hg,ht⟩:=h; exact ⟨⟨_,(e.fair_loose k).mul hp, fun i n h=> e.chuting k i (hq i n h)⟩,_,(e.fair_loose k).mul hg,fun i n m h he=> by rw [mul_assoc]; apply e.chuting k i (ht i n m h he)⟩
-- only α constant used
lemma shift_base {X:Type}{u:ℕ→ℕ→Field ι X}{l:ℕ→ Pulse.Range X} (h:Balance.Base e Nat.le l u) : Balance.Base e Nat.lt (fun i=>l (i+1)) (fun i n=>u (i+1) n):= by obtain ⟨p,hp,h⟩:=h; exact ⟨_, hp.next,fun i n h'=> h _ _ h'⟩
lemma shifts {X:Type}{u:ℕ→ℕ→Field ι X}{l:ℕ→ Pulse.Range X} (h:Balance.Stable e Nat.le l u): Balance.Stable e Nat.lt (fun i=>l (i+1)) (fun i n=>u (i+1) n):= by
   obtain ⟨p,hp,hv⟩:= h.2; refine ⟨e.shift_base h.1,_,hp.next.mul (e.fair_z.admits (q:=e.turn) (fun i=> (Real.exp_pos _).le) (Eventually.of_forall e.turn_bound)), fun i n m hn hm=>?_ ⟩; rw [mul_assoc,← η_spin]; exact hv _ n m hn hm
lemma range_shrink i (x:ι→Node X) : (bath (e.ξ i) k X).bill x ≤ (bath (e.flag i/2) k X).bill x:= by
    apply monoTerrace le_rfl _; have hp:= e.halos i; unfold haloSpan at hp; apply NNReal.coe_le_coe.mp; norm_cast at *; -- fails
    have he:= NNReal.coe_le_coe.mpr hp; push_cast at he; linarith only [he, NNReal.coe_nonneg (e.flag i)]
end chute
end Oasis
end Reserve
end
end YM.Contacts.Barrage
