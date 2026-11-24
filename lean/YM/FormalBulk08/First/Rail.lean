import YM.FormalBulk08.First.Dollars
/-!
 Clause: common full unnormalized log weights through E, always UNMASKED,
 rollback against existing trajectory on its own stage price. kvtmom growth
 on formal coefficient class itself does NOT require render against trajectory.
 `capitalX` includes *explicit* actual step theta cost. No claim of transfer
 in an actual EBound norm.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.First
open Function Filter Set Lattice RG Exterior Wilson Precision
open Stationary hiding shine Rays
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine Dove North Aster
open Next.Foundations PhysicalNext.Repeat.Legato
open Borough RG.Supply Push.PriceCompiler Dove.Lab
variable {G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{A:Levels G}{C:Family G}{W:Borough.Window G K}
lemma topRate (A:Levels G) (m:ℕ): 0≤A.clock.loopCap m ∧ A.clock.loopCap m ≤ 2*A.clock.monitor m := by
    have he: 1 ≤ A.clock.monitor m:= Real.one_le_exp (sq_nonneg _)
    have ht:=A.fits.thetaRange m; unfold Calendar.loopCap; refine ⟨mul_nonneg (by norm_num) (Real.rpow_nonneg (zero_le_one.trans he) _),?_⟩; refine mul_le_mul_of_nonneg_left ((_root_.Real.rpow_le_rpow_of_exponent_le he (show A.clock.theta _≤1 from ?_)).trans_eq (Real.rpow_one _)) (by norm_num); exact ht.2.trans (inv_le_one_of_one_le₀ (by exact_mod_cast (show 1≤A.clock.J m from le_trans (by omega) (A.clock.adm m))))
variable (L:∀ i,Lodge ((C.path.levels.clock.op i 0).patch))
variable (hG:G.Simple)(a:hue G)(h:LocalRatio ρ)(p:Provenance G C ρ){ℓ j E:ℕ}
section
variable (s:Borough.Window G C.path.levels.clock.kernel)(e:Evergreens C.path.levels.clock.kernel Spigot.herald C.labels.level C.params ρ s C.path.levels)(hx:Dahlia C.path.levels s.width)
include h p hG a e hx
lemma installs (J ℓ:ℕ)(hj:5≤J)(hf:J≤ C.path.levels.clock.J (ℓ+1)) (E:ℕ)(hE: E≤J)(hu:2≤E):∃ K:Leaf (cbook L ℓ s (lyre C.path.levels)).scrolls→ℝ, Soft (chron _) K ∧ ∀ x:Leaf (cbook L ℓ s (lyre C.path.levels)).scrolls,let S:= C.path.levels; let m:=x.b; let p':= S.params m; let σ:=s.width (S.clock.J m); let v:=K x * (1+ 2*S.clock.monitor m); let μ:=prints G p' E σ
     μ⁻¹ ≤ ageZ (S.clock.hatBeta m) ∧ ∀ N q:ℕ,m≤N → let R:=(C.path.rep N q m).path; let Y:=Dove.model S L (Hay.Wday S) ρ a N m
        ∃ (T:Pot G)(P:List (LeafD G)), Hay.Troupe T p'.clip R ∧ Broc.Fits T E μ v ∧ 0<μ ∧ PrintK (Y-T) E 3 (E-2) μ v P ∧ ∀ n: Side,Through E (stone Y n) (Hay.novel p'.clip R n+(P.map (fun a=>Broc.mountain (issue a.field) n a.u)).sum):= by
    obtain ⟨V,M,Q,D,O,ht,hV,hP⟩:=p.vacuum
    let A:= C.path.levels; let F:= cbook L ℓ s (lyre A); let u (x:Leaf F.scrolls):=s.width (A.clock.J x.b); have hq:Poster _ _ _ _ _ F J:= presold (Q:=Spigot.herald) (W:=s) (U:=F.toEmpire) hG (fun i=>show Evergreens C.path.levels.clock.kernel Spigot.herald C.labels.level C.params ρ s (F.V i) from e) F.neck hj (fun _=>hf)
    let R (x:Leaf F.scrolls):= money G (A.params x.b) E (u x); have hw x: |R x| ≤ ageZ (A.clock.hatBeta x.b) := le_trans (le_max_left ..) (hx.boots _ _ (hE.trans (hf.trans (A.fits.mono (show ℓ+1 ≤ x.b+1 from Nat.add_le_add_right x.zone _)))))
    have hz : Soft (chron F.scrolls) R:= (soft_day _).below (fun x=> by change |R x| ≤ |(lyre A).day x.b|; rw [measure e];exact (hw _).trans (le_abs_self _))
    obtain ⟨B,hB,hC,T⟩:= holdings (hq.vac E hE) h hG a
    refine ⟨_, hz.plus ((hB.plus hz).times hz),fun x=> ?_⟩; intro S m p' σ v μ
    have ho:= topRate S m; let k:=2*S.clock.monitor m; have hh:0≤k:=ho.1.trans ho.2; have hk:|μ⁻¹| ≤ _ := (le_max_right |R x| |μ⁻¹|).trans (hx.boots m _ (hE.trans (hf.trans (A.fits.mono (show ℓ+1 ≤ m+1 from Nat.add_le_add_right x.zone _)))))
    refine ⟨(le_abs_self _).trans hk,fun N q hm=> ?_⟩; intro R' Y;
    have he:R'=M.path N m:=hV N q m hm; rw [he]
    obtain P:= sold p' _ hu hG σ (s.pos (A.clock.J m)); obtain ⟨Y',hY,hp',H'⟩:= P.buys (M.path N m) (S.clock.loopCap m) (ht.cap N m hm) ho.1
    have hp:R x≥0:=P.positive; have hC' : Broc.Fits Y E σ (B x):=((T x).2 N hm).1
    obtain ⟨P',ht'⟩:= H' Y (B x) hC' (Temper.frame (genu A L (Hay.Wday A) _ a h hG hm) _) (Sane.frame (genu A L (Hay.Wday A) _ a h hG hm) _) (Hay.mature L h hG ht N a m hm Y' hY)
    have hx : (1+S.clock.loopCap m)*R x ≤ v := by
         apply ((mul_le_mul_of_nonneg_right (add_le_add_right ho.2 1) hp).trans ?_); unfold v
         rw [mul_comm (1+2*S.clock.monitor _)];exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg (add_nonneg (hC x) P.positive) P.positive)) (add_nonneg zero_le_one hh)
    have hz : (B x+(1+S.clock.loopCap m)*R x)*R x≤ v:= by
         have hg:B x+(1+S.clock.loopCap m)*R x ≤ (1+k)*(B x+R x):= by
           rw [mul_add]; apply add_le_add (le_mul_of_one_le_left (hC _) (le_add_of_nonneg_right hh)); exact mul_le_mul_of_nonneg_right (add_le_add_right ho.2 1) hp
         refine ((mul_le_mul_of_nonneg_right hg hp).trans ?_); rw [mul_assoc,mul_comm (1+k)]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hp) (add_nonneg zero_le_one hh)
    refine ⟨Y',P',hY,hp'.mono le_rfl hx,P.size,ht'.mono le_rfl hz, Hay.extra_seen ht' hu hY hC' hp' (s.pos _).le P.size.le⟩
end
end YM.FormalBulk08.First
