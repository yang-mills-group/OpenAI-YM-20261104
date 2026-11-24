import YM.OPE.Compatible.Tillage.Stamp
/-!
# Local wallet. Loans for repeated L. Purchases fixed after L choices wrt this horizon. J≥5 for vol.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G} {H:Seasons B}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier
variable (P B)
lemma pitchUp (B: Sponsor G) (P:Patch): ∃ s D:ℝ,0<s∧ ∀ v: Train P.J,(linesOf (ship P v) B.K.penalty).strip s D:=by
   obtain ⟨σ,C,hσ,hC,h⟩:= Planned.PrimaryIntegral295.Carrier.priced B.K.penalty B.K.penalty_pos P.order_cut P.order_cut; exact ⟨σ,C/(P.L.val:ℝ)^1,hσ,fun v=>h (ship P v) [] (by simp)⟩
variable {P B}
def charmSeal (C: Medal P G K P.J)(v: Train P.J): Boxes G P K:=⟨P.J,P.order_cut,C,v⟩
lemma drone (P:Patch)(B:Sponsor G)(C:Medal P G B.K P.J)(v:Train P.J):Kine (charmSeal C v) (linesOf (ship P v) B.K.penalty):=by
    obtain ⟨m,hm,H⟩:=naturalHigh P B.K (B.affordable P); refine ⟨m,hm,fun i=>?_⟩; let f:=ship P v; let S:= f.visit B.K (c:=m i) (f:=m i*P.L) rfl; exact C.trueMean S P.odd_side v (H i) P.order_cut (Flight.tangent f B.K P.order_cut (c:=m i) (f:=m i*P.L) rfl).1
section
variable (P) (C:Medal P G B.K P.J) {V:ChartRatio G}
lemma interlock (M:Alps B H P.J s)(N:Alps B H P.J u)(h: Charm P.L M N z V): N.gear=(ship P M.gear).land:=by
   obtain ⟨a,he,hx,hy,h⟩:=h.ink; rw [hy,hx]; let f:=a.wing; rw [show ship P a.wing=a from ?_]; cases a; cases he; rfl
lemma colorshift (M:Alps B H P.J s)(N:Alps B H P.J u)(h: Charm P.L M N z V)(hx:LocalRatio V): TEX (charmSeal C M.gear) M.clip N.clip M.live N.live z V:=by
   obtain ⟨A,hA,hV,he,hp⟩:=h.ink; have heq:A=ship P M.gear:=by rw [hV]; cases A; cases hA; rfl
   exact Votive.elevation (ship P M.gear) h.mag M N rfl (heq ▸ he) (heq ▸ hp) hx C
end
-- crest frame
section
variable (G P K)
def tariffs (n m:ℕ):Prop:=∀ (v:Train P.J)(X: Script (Shade G) (n+1)) a,soot m X a→ Poll X (4-n)→ X.pinned→soot m (Script.mat G.ColorIndex (ship P v) K.penalty X) ((1/4:ℝ)*a)
structure Crest (m:ℕ) : Prop where
   mark : 3≤m
   rows : ∃ s C D U:ℝ, Payer K P s C D U
   Tri : tariffs G P K 2 m
   Quad : tariffs G P K 3 m
   Bi : tariffs G P K 1 m
variable {P}
lemma targets (j:ℕ)(hj:5 ≤ j)(n m:ℕ)(hn:0 < n)(hv:n ≤ 3)(hm:3≤m): ∃ r:ℕ,∀ (L:Side), r ≤ L.val →∀ (ho:Odd L.val)(hx:3 ≤ L.val),tariffs G (⟨L,j,by omega,hx,ho⟩:Patch) K n m:=by
    obtain ⟨C,hC,h⟩:=volMat G.ColorIndex (j:=j) (k:=j) K.penalty_pos (by omega) (by omega) (n:=4-n) (m:=m) (by omega) (by omega) n
    obtain ⟨r,hr⟩:= exists_nat_gt (4*C); refine ⟨r,fun L hL ho hb v X a hs hz hp=> ?_⟩
    let P:Patch:=⟨L,j,by omega,hb,ho⟩; apply (h (ship P v) a X hs hz hp).tips; apply mul_le_mul_of_nonneg_right _ hs.coins; change C*(L.val:ℝ)^4 / (L.val:ℝ)^(n+1+(4-n))≤ _; rw [show n+1+(4-n)=5 from by omega, div_le_iff₀ (by positivity : 0 < (L.val:ℝ)^5)]; have hz : C≤ (1/4:ℝ)*L.val:= by
       have he:r ≤ (L.val:ℝ):=by exact_mod_cast hL
       linarith
    exact le_trans (mul_le_mul_of_nonneg_right hz (by positivity)) (le_of_eq (by ring))
lemma patroness (j m:ℕ)(hj:5≤j)(ht:3≤m):∃ r:ℕ,∀ (L:Side), r ≤ L.val →∀ (ho:Odd L.val)(hx:3 ≤ L.val), Crest G (⟨L,j,by omega,hx,ho⟩:Patch) K m:=by
    obtain ⟨t,c,d,b,hs,hc,hd,h,hp,hV⟩:=season K j (by omega)
    obtain ⟨r,hr⟩:= exists_nat_gt (2*ded t c b); choose a ha using targets G K j hj 1 m (by omega) (by omega) ht; choose B hB using targets G K j hj 2 m (by omega) (by omega) ht; choose C hC using targets G K j hj 3 m (by omega) (by omega) ht
    refine ⟨r+a+B+C,fun L hL ho hx=> ⟨ht,⟨t,c,b,d,⟨hs,hd.le,h,hV,hp,?_⟩⟩,hB L (by omega) ho hx,hC L (by omega) ho hx,ha L (by omega) ho hx⟩⟩
    rw [div_le_iff₀ (by change (0:ℝ)< (L.val:ℝ); positivity)]; have hz:r ≤ (L.val:ℝ):= (by exact_mod_cast (show r ≤ L.val from by omega)); change _ ≤ (1/2:ℝ)*L.val; linarith
end
end Alps
end YM.OPE.Votive
