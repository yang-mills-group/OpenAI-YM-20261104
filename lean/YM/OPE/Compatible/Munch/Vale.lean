import YM.OPE.Compatible.Munch.Cup
/-! # temperate dependence of refunds on footprints and costumes. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Score Lav Limn
variable {G:Gauge} {X:Type}
section Inv
variable {Z:Zone X}{s c v u C β r:ℝ}
variable {A B:X→price}{t z a:X→ℝ}
lemma Fξ_I (h:Z.Invoice t): Z.Invoice (fun x=> Fξ G s c u C (t x)):= by unfold Fξ; exact (Zone.Invoice.const (E:=ℝ) _).mul ((Zone.Invoice.const (E:=ℝ) _).mul h) -- const evar taker need explicit
lemma FWind_I (h:Z.Invoice t): Tunable Z (fun x=> FWind G s c u C (t x)):=by
       intro i; let p:=fun x=> Pξ G s c u C (t x); have hP : Z.Invoice p:= by unfold p Pξ; exact (Zone.Invoice.const (E:=ℝ) _).mul ((Zone.Invoice.const (E:=ℝ) _).mul ((Fξ_I h (G:=G)).add h))
       exact (h.add hP).add (Zone.Invoice.const _)
lemma Cσ_I (h:Z.Invoice t): Tunable Z (fun x=> Cσ G s c u C (t x)):=by
       intro i; exact ((Zone.Invoice.const (E:=ℝ) _).mul ((Zone.Invoice.const (2:ℝ)).mul h)).add ((Zone.Invoice.const (Soil G u s c C * Real.sqrt C*ampleP i)).add ((Zone.Invoice.const _).mul ((Fξ_I (G:=G) h).add h)))
lemma Hue_I (h:Tunable Z A)(he:Z.Invoice z): Tunable Z (fun x=> hueCost (A x) (z x) G):=fun i=> (he.mul (Zone.Invoice.const _)).mul (h i)
lemma Bfs_I (h:Z.Invoice z)(i:ℕ):Tunable Z (fun x=> Βuffs G s c C (roomV G i (z x))):=by
       intro j; have he : Z.Invoice (fun x=> roomV G i (z x)):= (h.mul (Zone.Invoice.const _)).add (Zone.Invoice.const _); exact (Zone.Invoice.const (2:ℝ)).mul (((he.mul (Zone.Invoice.const _)).mul (Zone.Invoice.const _)).mul (Zone.Invoice.const _))
lemma Tunable.row (h:Tunable Z A):Tunable Z (fun x=> J1+A x):=fun i=> (Zone.Invoice.const _).add (h i)
lemma Tunable.plus (h:Tunable Z A)(ht:Tunable Z B): Tunable Z (A+B):=fun i=> (h i).add (ht i)
lemma Tunable.bill (h:Tunable Z A)(he:Z.Invoice t): Tunable Z (fun x=> ‖t x‖ • A x):= fun i=> he.norm.mul (h i)
lemma Λ_B_I (h:Z.Invoice t)(hv:Z.Invoice z)(hx:Z.Invoice a)(n:ℕ):Tunable Z (fun x=> Λ_B G n s c u C (t x) (z x) (a x)) :=by
       have ht:=Hue_I (G:=G) (FWind_I (s:=s) (c:=c) (u:=u) (C:=C) (G:=G) h) hv; exact (((((ht.plus ht).row).row).hike _).bill hx).fuse (Hue_I (G:=G) (Cσ_I h) hv) -- Pi fun Issue
lemma Rise_I (h:Z.Invoice t)(he:Z.Invoice z)(hv:Z.Invoice a)(n:ℕ): Tunable Z (fun x=>RiseT G n s c u C (t x) (z x) (a x)):= (((Hue_I (G:=G) (FWind_I h) he).row).hike n).bill hv
lemma wind2I (n m:ℕ)(h:Z.Invoice t)(hz:Z.Invoice z)(he:Z.Invoice a): Z.Invoice (fun x=> price2 G n m s c u C (t x) (z x) (a x) r):= ((Zone.Invoice.const r).mul ((Jive_I (Rise_I h hz he n) (Λ_B_I h hz he n) (FWind_I h) (Cσ_I h) (Bfs_I hz 0) m).norm)).mul (Zone.Invoice.const (tokenCost G m (Gov s u)))
lemma wind3I (n m k:ℕ)(h:Z.Invoice t)(hz:Z.Invoice z)(he:Z.Invoice a): Z.Invoice (fun x=> price3 G n m k s c u C (t x) (z x) (a x) r r):= (((Zone.Invoice.const (r*r)).mul ((Alps_I k m (Rise_I h hz he n) (Λ_B_I h hz he n) (FWind_I h) (Cσ_I h) (Bfs_I hz)).norm)).mul (Zone.Invoice.const _)).mul (Zone.Invoice.const _)
lemma wallet_I (n:ℕ)(h:Z.Invoice t)(hz:Z.Invoice z)(he:Z.Invoice a): Z.Invoice (fun x=> wallet3 G n s c v u C (t x) (z x) (a x) β):= ((((Λ_B_I h hz he n 1).norm).add (((wind2I n 4 h hz he).norm).add ((wind2I n 2 h hz he).norm))).add ((wind2I n 3 h hz he).norm)).add ((wind3I n 3 3 h hz he).norm)
variable (G:Gauge)
lemma w45 (s c v u C β:ℝ)(n:ℕ): ∃ (S:ℝ)(F:ℕ),0 ≤ S ∧∀ (t z a:ℝ), ‖wallet3 G n s c v u C t z a β‖ ≤ S*(1+(‖t‖+(‖z‖+‖a‖)))^F:=by
       let Z:=Radial.zone (E:=ℝ×(ℝ×ℝ)); let T:=Prod.fst (α:=ℝ) (β:=ℝ×ℝ); let Q(x:ℝ×(ℝ×ℝ)):=x.2.2; have hx : Z.Invoice T:=⟨1,1,by norm_num,fun x=>by change ‖x.1‖ ≤ 1* (1+max ‖x.1‖ ‖x.2‖)^1; linarith [le_max_left ‖x.1‖ ‖x.2‖]⟩ -- issue type U
       have hu(p: (ℝ ×(ℝ×ℝ))→ℝ)(h:∀ x,‖p x‖≤ ‖x.2‖): Z.Invoice p:=⟨1,1,by norm_num,fun x=> (h _).trans (by change _≤ 1*(1+max ‖x.1‖ ‖x.2‖)^1; linarith [le_max_right ‖x.1‖ ‖x.2‖])⟩
       obtain ⟨S,F,hS,hp⟩:=wallet_I n (G:=G) (s:=s) (c:=c) (v:=v) (u:=u) (C:=C) (β:=β) hx (hu (Prod.fst ∘ Prod.snd) (fun x=>le_max_left ‖x.2.1‖ ‖x.2.2‖)) (hu Q (fun x=>le_max_right ‖x.2.1‖ ‖x.2.2‖)); refine ⟨S,F,hS,fun t z a=> (hp (t,z,a)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (Z.high _)) ?_ F) hS)⟩; change 1+max _ (max _ _)≤1+ (‖t‖+(‖z‖+‖a‖)); simp only[_root_.add_le_add_iff_left,max_le_iff]; have ht:=norm_nonneg t; have hz:=norm_nonneg z; have ha:= norm_nonneg a; exact ⟨by linarith,by linarith,by linarith⟩
end Inv
end YM.OPE.Borealis.Galea
