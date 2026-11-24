import YM.WilsonCoeffUV.Product.Report.Age
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Tested product estimate at capture mesh
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b b' u m M N a:ℕ}{H:Hol G} {x δ Z y:ℝ} {E W V' W':Credit}{R:Realm G (e+1) E}
variable {Q: Fin (a+1)→ SealR G}{T: Wilt Q}{P:Fin (a+1)→ℝ}{X Y:Herit Q}
lemma Sitting.selfX (v:Sitting Q P e δ X Y)(p:0≤δ): Sitting Q P e δ X X:=⟨v.stock,fun i j k h=>⟨(v.track i j k h).main,(v.track i j k h).main,by rw [sub_self,norm_zero]; exact mul_nonneg (v.stock i) p⟩⟩
lemma Sitting.rot (v:Sitting Q P e δ X Y): Sitting Q P e δ Y X:=⟨v.stock,fun i j k h=>⟨(v.track i j k h).side,(v.track i j k h).main,(by rw [norm_sub_rev]; exact (v.track i j k h).gap)⟩⟩
lemma Fringed.rot {S T:Era G ℝ}(p:Fringed k e u 1 A δ S T): Fringed k e u 1 A δ T S :=by
   refine ⟨p.pen,p.inkV,p.crest,fun i j h=>?_⟩; let Z:=p.heapS i j h; refine ⟨Z.wane,Z.wax,?_⟩; simpa only [neg_one_smul,neg_sub,abs_neg,abs_one,one_mul] using (Z.toll.μ (-1))
lemma Fringed.stow {S:Era G ℝ}(v:Fringed k e u 1 A δ S S)(z:A ≤ B)(t:A ≤ B*δ): Fringed k e u 1 B δ S 0 :=by
   have ht:Fringed k e u 1 (0:ℝ) δ (0:Era G ℝ) 0:= Fringed.nullV v.crest le_rfl
   refine ⟨v.inkV,ht.pen,v.crest,fun i j p=>?_⟩; let V:= v.heapS i j p; refine ⟨V.wax.more z,Fruit.zero.more (v.nn.trans z),?_⟩; change Fruit _ _ _ (_-0) _; rw [sub_zero]; exact V.wax.more t

-- for seams outside overlap, delta buys them through this radius
open Real
lemma thicker (S:Schedule)(p:b≤ i): trailC S m i ≤ trailC S m b:=by unfold trailC; rw [exp_le_exp]; linarith only [scales S p]
lemma borderW (S:Schedule)(p:m≤ i): paceT S m i ≤ trailC S m i ∧ paceT S m i ≤ trailC S m i*trailC S m i:=by
   unfold trailC; rw [← Real.exp_add,pace_rep]; exact ⟨Real.exp_le_exp.mpr (by linarith [scales S p]),Real.exp_le_exp.mpr (by linarith [scales S p])⟩
lemma patrol (S:Schedule)(m i:ℕ): trailC S m (m+i)≤ exp (-1/4)^i:= by
    unfold trailC; rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
    have hp:=winterH S (show m≤ m+i by omega); rw [show m+i-m=i by omega] at hp; unfold snowP at hp; linarith

def stopX (A:Levels G)(Ñ:ChartRatio G)(F:Wilt Q)(X:Herit Q)(m i N:ℕ)(y:ℝ)(o:CellR) := if i<N then Blizzard A Ñ F X m i N y o else 0
lemma PalmR (H:Hol G)(Q: Fin (a+1)→ SealR G)(E W V W' L:Credit)(e u:ℕ): ∃ C:Credit,∀ (R:Realm G (e+1) E), HorizonP H R W V Q→ SpringD R (capP Q) u (capP Q+2) W'→ Dormitory R (capP Q) u L→ ∀ m i b N M (F:Wilt Q)(X Y:Herit Q)(A B: Fin (a+1)→ℝ) (Z y δ)(o:CellR), R.anchor ≤ m → m≤ i → m≤ b→ b≤N → b≤M → R.y m≤ Z → Bough Q F y Z B → R.tempC m b ≤ δ → Sitting Q A e δ X Y →
    let T:= ∏ i,B i*A i; Fringed (capP Q) e u 1 (C.buy Z*R.tempC m i*T) δ (stopX R.draws R.paid F X m i N y o) (stopX R.draws R.paid F Y m i M y o):=by
   obtain ⟨C,hC⟩:= PalmDay H Q E W V W' L e u
   refine ⟨C,fun R Q' p t m i b N M F X Y A B Z y δ o hm hi hb hn hM hz hy hδ l=>?_⟩; intro T
   let S:=R.draws.S; let x:= paceT S m i; let V:= R.tempC m i; let A':= C.buy Z*V*T; let B':= C.buy Z*x*T; have ha:0≤C.buy Z:=zero_le_one.trans (C.purchase hy.pos)
   have hh:0≤δ:= (trail_pos ..).le.trans hδ; have hT:0≤ T:= Finset.prod_nonneg fun i _=> mul_nonneg (hy.lanes i).1 (l.stock i); have hv:0≤V:= (trail_pos ..).le
   have hz:B'≤ A':= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (borderW S hi).1 ha) hT
   have he (q:b≤ i): B'≤ A'*δ:=by
       have hf:= (borderW S hi).2; have hd: V≤δ:= (thicker S q).trans hδ
       calc
           _ ≤ C.buy Z*(V*δ)*T := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hf.trans (mul_le_mul_of_nonneg_left hd hv)) ha) hT
           _ = A'*δ:=by unfold A'; ring
   let Lb:= max (i+1) b; have hp : i<Lb:= (Nat.le_max_left ..); have hu:R.tempC m Lb≤ δ:= (thicker S (Nat.le_max_right ..)).trans hδ
   unfold stopX; split
   · rename_i w; split
     · rename_i z; exact (hC R Q' p t m i Lb N M F X Y A B Z y δ o hm hi hp (max_le w hn) (max_le z hM) (by assumption) hy hu l).pay hz
     rename_i z; exact (hC R Q' p t m i Lb N N F X X A B Z y δ o hm hi hp (max_le w hn) (max_le w hn) (by assumption) hy hu (l.selfX hh)).stow hz (he (by omega))
   rename_i w; split
   · rename_i z; exact ((hC R Q' p t m i Lb M M F Y Y A B Z y δ o hm hi hp (max_le z hM) (max_le z hM) (by assumption) hy hu (l.rot.selfX hh)).stow hz (he (by omega))).rot
   exact Fringed.nullV hh (mul_nonneg (mul_nonneg ha hv) hT)
abbrev loadK (A:Levels G)(Ñ:ChartRatio G)(F:Wilt Q)(X: Herit Q)(m i N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:= cruises A Ñ N (capP Q) i m (Ashore Q A Ñ F X m i N y o)
lemma tip_pay (P:HorizonP H R W V' Q)(F:Wilt Q)(X:Herit Q)(t:R.anchor ≤ m)(p:m≤ i)(_v:m≤ N)(o:CellR) :
   let C i:= loadK R.draws R.paid F X m (min i N) N y o; C (i+1)= C i + stopX R.draws R.paid F X m i N y o:=by
   intro C; unfold stopX; split
   · rename_i h; let A:=R.draws; let S:=R.paid; let Z n:= Ashore Q A S F X m n N y o
     have hp:= ash_head P F X (y:=y) (m:=m) (t.trans p) h.le o; have hx:= ash_head P F X (i:=i+1) (y:=y) (m:=m) (t.trans (by omega)) h o
     have he:= cruisePlus A p R.hG R.green (Nat.le_of_lt h) (Auth.verse A h R.hG R.green hx) hp
     unfold C loadK Blizzard; rw [ash_tide P F X t p h o, min_eq_left h,min_eq_left h.le, he,cruiseStep A _ _ p]; abel
   rename_i h; unfold C; rw [min_eq_right (by omega),min_eq_right (by omega),add_zero]
lemma topDay (H:Hol G)(Q: Fin (a+1)→ SealR G)(E W V W' L:Credit)(e u:ℕ): ∃ C:Credit,∀ (R:Realm G (e+1) E), HorizonP H R W V Q→ SpringD R (capP Q) u (capP Q+2) W' → Dormitory R (capP Q) u L → ∀ m i b N M (F:Wilt Q)(X Y: Herit Q)(A B: Fin (a+1)→ℝ)(Z y δ)(o:CellR), R.anchor ≤ m→ m≤ i → m≤ b → b≤N → b≤ M →R.y m≤ Z → Bough Q F y Z B → R.tempC m b≤ δ → Sitting Q A e δ X Y →
   let T:= ∏ i,B i*A i; Fringed (capP Q) e u 1 (C.buy Z*T) δ (loadK R.draws R.paid F X m (min i N) N y o) (loadK R.draws R.paid F Y m (min i M) M y o):=by
   obtain ⟨S,hS⟩:=PalmR H Q E W V W' L e u; obtain ⟨V0,hV⟩:= regionPay H Q E W V e u
   let x:=exp (-1/4); have hx:0<x:=Real.exp_pos _; have hp:x<1:= Real.exp_lt_one_iff.mpr (by norm_num); let c:=(1-x)⁻¹; have hv:0<c:= inv_pos.mpr (sub_pos.mpr hp)
   let C:= V0.plus (S.prodC (pur c)); refine ⟨C,fun R H' p t m i b N M F X Y A B0 Z y δ o hm hi hb hn hM hz hy hδ l=>?_⟩; intro T
   let P n:=loadK R.draws R.paid F X m (min (m+n) N) N y o; let Q' n:=loadK R.draws R.paid F Y m (min (m+n) M) M y o; let B:= S.buy Z*T; let D:= V0.buy Z*T; let U n:=D+B*c*(1-x^n); have hT:0≤T:= Finset.prod_nonneg fun i _=> mul_nonneg (hy.lanes i).1 (l.stock i); have h'':0≤ S.buy Z:= zero_le_one.trans (S.purchase hy.pos); have hB:0≤ B:=mul_nonneg h'' hT
   have hh n: Fringed (capP Q) e u 1 (U n) δ (P n) (Q' n):=by
      induction n with
      | zero=>
        unfold P Q' U loadK; simp only [min_eq_left (hb.trans hn),min_eq_left (hb.trans hM),cruises_top,pow_zero,sub_self,mul_zero,add_zero]
        have hQ: Compar R.draws.S R.y m m ≤ Z:=by simpa only [Compar,sub_self,add_zero,Nat.sub_self,Nat.cast_zero] using hz
        have h:=hV R H' m m b N M F X Y A B0 Z y δ o hm le_rfl hb hn hM hQ hy hδ l; simpa only [pace_self,one_pow,inv_one,one_mul] using h
      | succ n ih=>
        let d:=m+n; let Q0 n' a U:=loadK R.draws R.paid F U m n' a y o; have hv':m≤d:=by omega
        have hh' := (hS R H' p t m d b N M F X Y A B0 Z y δ o hm hv' hb hn hM hz hy hδ l); have heq:= (ih.plus hh' zero_le_one).pay (show _≤ U (n+1) from le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (patrol R.draws.S m n) h'') hT) _) (le_of_eq ?_))
        · have hN := tip_pay (y:=y) H' F X hm hv' (hb.trans hn) o; have hM:=tip_pay (y:=y) H' F Y hm hv' (hb.trans hM) o; unfold P Q'; dsimp only at hN hM; rw [show m+(n+1)=d+1 by omega, hN,hM]; exact heq
        change U n + S.buy Z*x^n*T = _; unfold U c B; have ht:1-x≠0:=ne_of_gt (by linarith); field_simp; ring
   have hK n: U n≤ C.buy Z*T:=by
       have hf: S.buy Z*c ≤ (S.prodC (pur c)).buy Z:=by rw [Credit.products]; exact mul_le_mul_of_nonneg_left (pure_goal ..) h''
       refine le_trans (add_le_add_right (show _≤ B*c from ?_) D) (le_trans ?_ (mul_le_mul_of_nonneg_right (Credit.fuel _ _ hy.pos) hT)); exact (show B*c*(1-x^n)≤ B*c from mul_le_of_le_one_right (mul_nonneg hB hv.le) (sub_le_self _ (by positivity))); unfold D B; rw [add_mul,mul_right_comm _ T c]; exact add_le_add_right (mul_le_mul_of_nonneg_right hf hT) _
   have hz' := (hh (i-m)).pay (hK _); unfold P Q' at hz'; rwa [Nat.add_sub_of_le hi] at hz'
end YM.WilsonCoeffUV.Mer
