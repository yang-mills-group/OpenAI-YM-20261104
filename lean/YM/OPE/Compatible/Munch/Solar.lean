import YM.OPE.Compatible.Munch.Cour
/-! # budget magnitude and currency gain. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Score Lav Limn
variable {G:Gauge} {X:Type}
section Inv
variable {Z:Zone X}{s c v u C β r:ℝ}
variable {A B:X→price}{t z a J:X→ℝ}
lemma Cav2_I (h:Z.Invoice t)(he:Z.Invoice z)(hx:Z.Invoice a)(ht:Z.Invoice J)(k m:ℕ): Z.Invoice (fun x=> Cave2 G k m s c u C (t x) (z x) (a x) (J x) r):=by
       have hU:=Rise_I (G:=G) (s:=s) (c:=c) (u:=u) (C:=C) h he hx k; have hp:=FWind_I (G:=G) (s:=s) (c:=c) (u:=u) (C:=C) h; exact ((Zone.Invoice.const r).mul ((clamp_I (Duo_I (hU 2) (hp.hike m 2)) ((hU 2).mul (hp.reel (Bfs_I he 0) m 2))).norm)).mul ((Zone.Invoice.const _).add (ht.mul (Zone.Invoice.const _)))
lemma Cav3_I (h:Z.Invoice t)(he:Z.Invoice z)(hx:Z.Invoice a)(ht:Z.Invoice J)(k m:ℕ): Z.Invoice (fun x=> Cave3 G k m s c u C (t x) (z x) (a x) (J x) r):=by
       have hU:=Rise_I (G:=G) (s:=s) (c:=c) (u:=u) (C:=C) h he hx k; have hp:=FWind_I (G:=G) (s:=s) (c:=c) (u:=u) (C:=C) h; have hk:=Alc_I hU hp (Bfs_I (G:=G) (s:=s) (c:=c) (C:=C) he) m m; have hh:= (hp.hike m 4);
       exact (((Zone.Invoice.const (r*r)).mul ((clamp_I (Tri_I (hU 4) hh hh) (clamp_I hk hk)).norm)).mul ((Zone.Invoice.const _).add (ht.mul (Zone.Invoice.const _)))).mul ((Zone.Invoice.const _).add (ht.mul (Zone.Invoice.const _)))
lemma Caver_I (h:Z.Invoice t)(he:Z.Invoice z)(hx:Z.Invoice a)(ht:Z.Invoice J)(k:ℕ): Z.Invoice (fun x=> Caver G k s c v u C (t x) (z x) (a x) (J x) β):= ((((Rise_I h he hx k 1).norm).add (((Cav2_I h he hx ht k 4).norm).add ((Cav2_I h he hx ht k 2).norm))).add ((Cav2_I h he hx ht k 3).norm)).add ((Cav3_I h he hx ht k 3).norm)
lemma offered_W (G:Gauge)(s c v u C β:ℝ)(k:ℕ): ∃ (D:ℝ)(n:ℕ),0≤D ∧∀ J z a t:ℝ, Caver G k s c v u C t z a J β ≤ D*(1+(‖J‖+‖z‖+‖a‖))^n*(1+‖t‖)^n :=by
        let Z := Radial.zone (E:=(ℝ×ℝ)×(ℝ×ℝ)); let A(p:(ℝ×ℝ)×(ℝ×ℝ)):=p.1.1; let B(p:(ℝ×ℝ)×(ℝ×ℝ)):=p.1.2; let V(p:(ℝ×ℝ)×(ℝ×ℝ)):=p.2.1; let X(p:(ℝ×ℝ)×(ℝ×ℝ)):=p.2.2
        have hv(p: (ℝ×ℝ)×(ℝ×ℝ)→ℝ)(h:∀ x,‖p x‖≤ ‖x‖): Z.Invoice p:=⟨1,1,by norm_num,fun x=> (h _).trans (by change _≤ 1*(1+‖x‖)^1; linarith)⟩
        obtain ⟨D,n,hD,hP⟩:= Caver_I (s:=s) (c:=c) (u:=u) (v:=v) (C:=C) (β:=β) (G:=G) (hv X (fun x=> (le_max_right ‖x.2.1‖ _).trans (le_max_right ‖x.1‖ ‖x.2‖))) (hv B fun x=> (le_max_right ‖x.1.1‖ _).trans (le_max_left ‖x.1‖ ‖x.2‖)) (hv V fun x=> (le_max_left _ ‖x.2.2‖).trans (le_max_right ‖x.1‖ ‖x.2‖)) (hv A fun x=> (le_max_left _ ‖x.1.2‖).trans (le_max_left ‖x.1‖ ‖x.2‖)) k
        refine ⟨D,n,hD,fun J z a t=>?_⟩; rw [mul_assoc D,←mul_pow]; apply ((Real.le_norm_self _).trans (hP ((J,z),(a,t)))).trans ; apply mul_le_mul_of_nonneg_left _ hD; apply pow_le_pow_left₀ (zero_le_one.trans (Z.high _)) _; change 1+max (max ‖J‖ ‖z‖) (max ‖a‖ ‖t‖) ≤ (1+_)*_; have ht : max (max ‖J‖ ‖z‖) (max ‖a‖ ‖t‖) ≤ ‖J‖+‖z‖+‖a‖+‖t‖:=by simp only[max_le_iff]; have hv:=norm_nonneg J; have hz:=norm_nonneg z; have ht:=norm_nonneg t; have h:=norm_nonneg a; exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
        nlinarith only [mul_nonneg (show 0 ≤ ‖J‖+‖z‖+‖a‖ by positivity) (norm_nonneg t),ht]
end Inv
end YM.OPE.Borealis.Galea
