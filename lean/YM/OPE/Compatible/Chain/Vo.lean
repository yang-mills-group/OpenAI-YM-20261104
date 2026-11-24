import YM.OPE.Compatible.Chain.Lore
/-!
# boost readout
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore
variable {C:KernelChoices}{r:ℕ}
variable (H:Even n.val)
local notation "TK" => Libra.Keys G (Limb H)
-- color lens compression
abbrev flightPart (p:G.ColorIndex) : TK→ₗ[ℝ] form 1 n where
    toFun v:= parts G 1 (cloak H v) p
    map_add' a b:= by funext i; rw [map_add]; rfl
    map_smul' a b:=by funext i; rw [map_smul]; rfl
lemma choice_flag (v:Train r)(h:4≤r):∃ A:Law TK,∀ x y,A.P x y=flag H (ShellRow C v) x y :=by
      let B(x:TK)(y):= flag H (ShellRow C v) x y
      have he:= flag_sym H h (C:=C) v (G:=G); have ht(x):∃ A:Dual' TK,B x=A:= by
         refine ⟨{toFun:=B x,map_add':=?_,map_smul':=?_},rfl⟩
         · intro a b; let M:= major (ShellRow C v) n; let f:= cloak H x; unfold B flag; dsimp only; simp_rw [show ∀ i:G.ColorIndex,parts G 1 (cloak H (a+b)) i=parts G 1 (cloak H a) i+parts G 1 (cloak H b) i from fun i=> (flightPart H i).map_add a b, mulVec_add,dotProduct_add,sum_add_distrib]; ring
         intro c a; unfold B flag; dsimp only; simp_rw [show ∀ i:G.ColorIndex,parts G 1 (cloak H (c • a)) i=c • parts G 1 (cloak H a) i from fun i=> (flightPart H i).map_smul _ _,mulVec_smul,dotProduct_smul,smul_eq_mul, RingHom.id_apply,← Finset.mul_sum];ring
      obtain ⟨U,hp⟩:=giraffe_addendum ht he; exact ⟨Libra.giraffe U (fun x y=>by rw [hp,hp]; exact he ..) (fun x hx=>hp x x ▸ flag_pos H h v x hx),hp⟩ -- direction
abbrev boost (v:Train r)(h:4≤r) (C:KernelChoices):Law TK:= Classical.choose (choice_flag H v h (C:=C))
lemma boost_price (v:Train r)(h:4≤r)(x y:TK) : (boost H v h C).P x y=flag H (ShellRow C v) x y:= Classical.choose_spec (choice_flag H v h (C:=C)) x y
abbrev MarkC (a:G.ColorIndex)(v: Body 1 n): Dual' TK := { toFun:= fun p=> flightPart H a p v,map_add':=fun x y=>congr_fun ((flightPart H a).map_add x y) v,map_smul':=fun c x=> congr_fun ((flightPart H a).map_smul c x) _}
-- realize solution to boosted covariance
abbrev clued (e:G.ColorIndex→form 1 n)(p:Limb H):G.Color:= toLp 2 fun i=> e i (addressR p.val)
lemma tenderPart (e:G.ColorIndex→ form 1 n)(h:∀ i k,stem k (e i)=e i)(a): parts G _ (cloak H (clued H e)) a=e a:=by
      funext i; obtain ⟨p,rfl⟩:= addressR.surjective i
      rw [show (parts G 1 (cloak H (clued H e)) a) (addressR p)=(hover H (clued H e) p) a from by unfold parts; rw [show addressR p=(p.1,coord p.2) from rfl,cloak_at,Prod.mk.eta]]
      unfold hover; let x:=pathX H p; let k:=(edgesK H).tick p; have hk: ferry k x.val=p:=(resettle H p).symm; have hu : stem k (e a) (addressR x.val)= _:= congr_fun (h a k) (addressR x.val)
      have he:(axisK k).flip x.val.2=dir H p:=congr_arg _ ((ferry_axis ..).symm.trans (congr_arg Prod.snd hk)); rw [stemR,hk,he] at hu; split <;> rename_i hx
      · rw [if_pos hx] at hu; change -e a (addressR x.val)=_; rw [← hu,neg_neg]
      rw [if_neg hx] at hu; exact hu.symm
lemma boostFleet (h:4≤r)(v: Train r)(q a:G.ColorIndex)(x y:Body 1 n):
     (boost H v h C).wick (MarkC H q x) (MarkC H a y)= if a=q then acrossH (lineC (ShellRow C v) n *ᵥ Pi.single x 1) y else 0:=by
          let B:= boost H v h C (G:=G); let M:=ShellRow C v; let L:= lineC M n; let F:= acrossH (L*ᵥ(Pi.single x 1)); let w(p:G.ColorIndex): form 1 n:=if p=q then F else 0; let t:TK:=clued H w
          have ht(p:G.ColorIndex): parts G _ (cloak H t) p=w p:= tenderPart H w (fun i k=> by unfold w; split; exact staid H (L*ᵥPi.single x 1) k; exact map_zero _) p
          have hp:B.P t = MarkC H q x:=by
             apply LinearMap.ext;intro u; rw [B.turns]; rw [show B.P u t= _ from boost_price ..]; unfold flag; dsimp only; simp_rw [ht]
             rw [sum_eq_single q (fun j _ hj=> ?_) (by simp)]; swap; · simp [w,if_neg hj]
             unfold w; rw [if_pos rfl]; let U:= parts G _ (cloak H u) q; rw [show _= _ from specter (C:=C) H h v (Pi.single x 1) U ((StemClip U).mpr (EllK H q u))] -- fix k name
             change _= U x; simp
          have hv: B.inverse (MarkC H q x)=t:= by rw [←hp,B.solves]
          change parts G _ (cloak H (B.inverse _)) a y=_; rw [hv,ht]; unfold w; split<;>rfl
end YM.OPE.Cascade.Terp
