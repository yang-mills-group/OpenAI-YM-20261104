import YM.WilsonCoeffUV.Vacuum.UV.Relation
/-! Window charges for relative variable powers and inverse formula. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U V W T:Credit}
variable {Ñ:ChartRatio G} {A: Levels G}
lemma angle_tilt (g:G.Simple)(h: LocalRatio Ñ)(p:m<N): constantCoeff (pitch A Ñ N m)=1:= (perch A Ñ g h p).calm

def relativeF (A:Levels G)(Ñ:ChartRatio G)(N m k:ℕ): Cost:= palmB (fun i=> ratioHigh A Ñ N (m+i)) k
def relativeC (A:Levels G)(Ñ:ChartRatio G)(N m k : ℕ): Cost:= leeB (fun i=> pace (pitch A Ñ N (m+i))) k
lemma direction (g:G.Simple)(h:LocalRatio Ñ)(p:m+k≤N): chartB (relativeF A Ñ N m k) (relativeC A Ñ N m k)=1 ∧ chartB (relativeC A Ñ N m k) (relativeF A Ñ N m k)=1 := deckDual _ _ (fun i hi=>chart_forward (angle_tilt g h (by omega))) (fun i hi=>chart_backward (angle_tilt g h (by omega)))
lemma angularF (g:G.Simple)(h:LocalRatio Ñ)(p:m+k≤N): constantCoeff (relativeF A Ñ N m k)=1 := cc_palm (fun i hi=>back_cc (angle_tilt g h (by omega)))
lemma angularC (g:G.Simple)(h:LocalRatio Ñ)(p:m+k≤N): constantCoeff (relativeC A Ñ N m k)=1 := cc_lee (fun i hi=>pace_cc (angle_tilt g h (by omega)))
lemma stageF (A:Levels G)(Ñ: ChartRatio G)(N m i j:ℕ): relativeF A Ñ N m (i+j) = chartB (relativeF A Ñ N (m+i) j) (relativeF A Ñ N m i):=by unfold relativeF; rw [palm_joins]; simp only [Nat.add_assoc]
lemma stageC (A:Levels G)(Ñ: ChartRatio G)(N m i j:ℕ): relativeC A Ñ N m (i+j)=chartB (relativeC A Ñ N m i) (relativeC A Ñ N (m+i) j):=by unfold relativeC; rw [lee_joins]; simp only [Nat.add_assoc]
lemma pitch_step (G:Gauge)(e:ℕ)(U:Credit)(i:ℕ)(w:i≤ e): ∃ T:Credit,∀ R:Realm G e U,∀ m (_:R.anchor≤ m) b N M,m<b→ b≤N→ b≤ M→ twain (R.cash T m) (R.tempC m b) (coeff i (pitch R.draws R.paid N m)) (coeff i (pitch R.draws R.paid M m)) := by
    obtain ⟨T,hT⟩:= advent G e U i 2 w
    refine ⟨T.prodC U, fun R m h b N M z p t=>?_⟩
    rw [pitch,pitch,stellar_read,stellar_read,Realm.cash,Credit.products]
    refine (note_kin (hT R m h b N M z p t) (R.mint m h).width).lift (mul_le_mul_of_nonneg_left (R.taxes m h).flash (zero_le_one.trans (T.purchase (R.depth _ h)))) (trail_pos ..).le

structure WindowS (G:Gauge)(e:ℕ)(U:Credit) where
    robe : Realm G e U
    base : ℕ
    span : ℕ
    n:ℕ
    N:ℕ
    b:ℕ
    root: robe.anchor ≤ base
    endS : base+span ≤ b
    hd: b≤n
    hg:b≤N
namespace WindowS
abbrev Age (I:WindowS G e U):= I.robe.y I.base + (I.robe.draws.S.scale (I.base+I.span)-I.robe.draws.S.scale I.base) + I.span
lemma covers (I:WindowS G e U){j:ℕ}(ha:j≤I.span): I.robe.y (I.base+j)≤ I.Age:= by
   unfold Age; have he:= I.robe.age I.base (I.base+j) I.root (by omega); have hh:= scales I.robe.draws.S (show I.base+j≤ I.base+I.span by omega); linarith
lemma buySpan (I:WindowS G e U): (I.span:ℝ) ≤ I.Age:=by unfold Age; have h:= scales I.robe.draws.S (Nat.le_add_right I.base I.span); have he:= I.robe.depth _ I.root; linarith
lemma warm (I:WindowS G e U): 1≤ I.Age:=le_trans (I.robe.depth _ I.root) (I.covers (Nat.zero_le _))
abbrev cab (I:WindowS G e U): ℝ:= I.robe.tempC (I.base+I.span) I.b
lemma payments (G:Gauge)(e:ℕ)(U:Credit): Brite (WindowS.Age (G:=G) (e:=e) (U:=U)) WindowS.cab:= ⟨warm, fun _=>(trail_pos ..).le⟩
end WindowS
lemma twain.wide {V:Type*}[NormedAddCommGroup V]{A δ κ:ℝ}{x y:V}(p:twain A δ x y)(h:δ≤κ): twain A κ x y:= ⟨p.main,p.side,p.gap.trans (mul_le_mul_of_nonneg_left h p.nn)⟩

section
variable (G e U) (i)
theorem ascend (ha:i≤ e): Weft (WindowS.Age (G:=G) (e:=e) (U:=U)) WindowS.cab (fun I=> relativeF I.robe.draws I.robe.paid I.n I.base I.span) (fun I=>relativeF I.robe.draws I.robe.paid I.N I.base I.span) i:= by
    let D:= WindowS G e U
    let Age:= WindowS.Age (G:=G) (U:=U) (e:=e)
    let θ:= WindowS.cab (G:=G) (U:=U) (e:=e)
    let s := WindowS.span (G:=G) (e:=e) (U:=U)
    let P (a:D)(k:ℕ) := pitch a.robe.draws a.robe.paid a.n (a.base+k)
    let Q (a:D)(k:ℕ):=pitch a.robe.draws a.robe.paid a.N (a.base+k)
    let f (a:D)(k:ℕ):= back (P a k); let g (a:D)(k:ℕ):= back (Q a k)
    have ht a k (hx:k<s a): k+a.base<a.b:= by change k< a.span at hx; have hv:=a.endS; omega
    have he a (k:ℕ)(hx:k<s a): constantCoeff (P a k)=1:= by
       have hz : a.base+k < a.n := by have hg:= ht a k hx; have he:=a.hd; omega
       exact angle_tilt a.robe.hG a.robe.green hz
    have h' a (k:ℕ)(hx:k<s a): constantCoeff (Q a k)=1:= by
       have hz : a.base+k < a.N := by have hg:= ht a k hx; have he:=a.hg; omega
       exact angle_tilt a.robe.hG a.robe.green hz
    have hc:= WindowS.payments G e U
    have H:Brite (rub s Age) (rub s θ):= ⟨fun i=>hc.large _,fun i=>hc.dist _⟩
    have hy k (hk:k≤ i): Weft (rub s Age) (rub s θ) (gemsP s P) (gemsP s Q) k:=by
        obtain ⟨T,hT⟩:= pitch_step G e U k (hk.trans ha)
        refine ⟨T.d,T.x,zero_le_one.trans T.good,fun v=>?_⟩; obtain ⟨a,j,hv⟩:= v
        have hz: a.robe.anchor ≤ a.base+j:=a.root.trans (Nat.le_add_right ..)
        have hr:= hT a.robe _ hz _ _ _ (show a.base+j < a.b by have he:=ht a j hv; omega) a.hd a.hg
        change j<a.span at hv
        refine ((hr.lift (T.elder (a.robe.depth _ hz) (a.covers hv.le)) (trail_pos ..).le).wide ?_); exact narrow _ (by change a.base+j≤ a.base+a.span; omega) _
    have hh:= shiny (A:=f) (B:=g) (i:=i) hc WindowS.buySpan (fun a j hx=>back_cc (he a j hx)) (fun a j hx=>back_cc (h' a j hx)) (fun j hj=> clipped_back (p:=gemsP s P) (q:=gemsP s Q) H (fun i=>he i.cargo i.coin i.credit) (fun i=>h' i.cargo i.coin i.credit) fun k hk=> hy k (hk.trans hj))
    obtain ⟨d,t,hT,E⟩:= hh; exact ⟨d,t,hT, fun a=> E ⟨a,a.span,le_rfl⟩⟩
theorem descend (ha:i≤e): Weft (WindowS.Age (G:=G) (e:=e) (U:=U)) WindowS.cab
    (fun I=> relativeC I.robe.draws I.robe.paid I.n I.base I.span)
    (fun I=>relativeC I.robe.draws I.robe.paid I.N I.base I.span) i:=
    clipped_dual (WindowS.payments G e U)
    (fun j=>angularF j.robe.hG j.robe.green (j.endS.trans j.hd))
    (fun j=>angularF j.robe.hG j.robe.green (j.endS.trans j.hg))
    (fun j hj=>ascend G e j U (hj.trans ha))
    (fun j=> (direction j.robe.hG j.robe.green (j.endS.trans j.hd)).1)
    (fun j=> (direction j.robe.hG j.robe.green (j.endS.trans j.hg)).1)
-- optional unify and remove n cost if scale known.
lemma arc_span (S:Schedule)(m k:ℕ): (k:ℝ)*Real.log 3 ≤ S.scale (m+k)-S.scale m:=by
   induction k with
   | zero=> simp
   | succ k ih=> have he:= arch_pos S (m+k); unfold PathCost.arc at he; rw [show m+(k+1)=m+k+1 by omega]; push_cast; linarith
end
end YM.WilsonCoeffUV.Bank
