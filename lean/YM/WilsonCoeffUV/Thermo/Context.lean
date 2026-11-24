import YM.WilsonCoeffUV.Thermo.Primitive
import YM.WilsonCoeffUV.Step.Interlace
/-!
# The bulk unrotated recursion is the same chart at every step
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Next.Free Tree PowerSeries AnalyticNext.QuarticMatch.Sheets
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{L c n f:Side} {α β V ι : Type*}{k r l j:ℕ} {P:Patch}

section patch
variable (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)
variable (H Y:FaceRow)(W:Crude G)(Q:(n:Side)→ Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)

abbrev mStep (A: Levels G)(c:Side)(m:ℕ) := stepAt (loose A m) A.clock.kernel c
abbrev xree (P:Patch)(K:KernelChoices)(n:Side):= repeatF (stepAt P K n)
abbrev mer (P:Patch)(K:KernelChoices)(H:FaceRow)(n:Side):= covariance G (stepAt P K n) (xree P K n) H
abbrev teller (G:Gauge)(P:Patch)(K:KernelChoices)(Q:(n:Side)→ Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ) (n:Side) := extractV G (stepAt P K n) (xree P K n) (Q n)
local notation "Cℕ" => Larvae G P.L
local notation "Hℕ" => Hinge G P.L
local notation "S▪" => fun n=>stepAt P K n
local notation "I▪" => fun n=> weaveFine (ratioN P.L n) G
local notation "T▪" => fun n=> weaveH (ratioN P.L n) G

lemma whyPack (n: Side) (x y:ℕ) :
    let S:= S▪ n; let F:= xree P K n; let T:= T▪ n; let M:=allotM (I▪ n) (I▪ n) (mer (G:=G) P K H n)
    bend T (xray S F H (Q n) Ñ (W (n*P.L)) x y)= abr (stair (upper (β:=Hooks G) M 0) 0) (fun j=>bend T (casePW S Ñ (teller G P K Q n) (W (n*P.L)) j)) x y:=by
  intro S F T M; have he: allotM T T (fillSlots (Woods G n) (mer (G:=G) P K H n))=stair (upper (β:=Hooks G) M 0) 0:= lamp_chart _ (mer (G:=G) P K H n)
  rw [← he]; exact bend_abr ..
lemma season_fold (n i) : summer (S▪ n) (xree P K n) H (Q n) Ñ (W (n*P.L)) i= sluice (∑ j∈ Finset.range (3+3*i),bend (T▪ n) (xray (S▪ n) (xree P K n) H (Q n) Ñ (W (n*P.L)) j i)):=by
  rw [← bend_sum]; exact into_shade (ratioN P.L n) _

-- supply from outside
structure PaintKit (P:Patch)(K:KernelChoices)(G:Gauge)(H:FaceRow)(Q:(n:Side)→ Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ) (Γ: ropes Cover (Larvae G P.L) (Larvae G P.L))(M: ropes Cover (Larvae G P.L) (Hooks G)): Prop where
  toll : Pilots (fun n=> allotM (weaveFine (ratioN P.L n) G) (weaveFine (ratioN P.L n) G) (mer (G:=G) P K H n)) Γ
  mark : Pilots (fun n=> allotM (weaveFine (ratioN P.L n) G) (Equiv.refl (Woods G n)) (teller G P K Q n)) M

set_option maxHeartbeats 600000 in
lemma spurs_enter {Z:Canvas G}{Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}(e:P.Branches K G)(h:LocalRatio Ñ)(p:∀ i r,Yields (fun n=>W n i r) (Z i r)) (F:PaintKit P K G H Q Γ M)(x y r):
    Yields (fun n=> bend (weaveH (ratioN P.L n) G) (xray (stepAt P K n) (xree P K n) H (Q n) Ñ (W (n*P.L)) x y) r) (spurs P K Ñ Γ M Z x y r):= by
  let X (n:Side) (i): Gen ℝ (Co n (Hinge G P.L)):=bend (weaveH (ratioN P.L n) G) (casePW (stepAt P K n) Ñ (teller G P K Q n) (W (n*P.L)) i)
  let D (n:Side) : ropes (Site n) (Hinge G P.L) (Hinge G P.L):= stair (upper (allotM (weaveFine (ratioN P.L n) G) (weaveFine (ratioN P.L n) G) (mer (G:=G) P K H n)) 0) 0
  have hb : Pilots D (stair (upper Γ 0) 0):= ((F.toll.deck (Pilots.silent (β:=Hooks G))).deck' (Pilots.silent (α:=Hooks G)))
  have ha i r : Yields (fun n=> X n i r) (stellar P K Ñ M Z i r):= star_pages (P:=P) (W:=W) (Z:=Z) (T:=teller G P K Q) K F.mark h e i r (p i r)
  have he:= tide_pages (P:=X) (α:=Hinge G P.L) hb ha x y r
  have hz n: bend (weaveH (ratioN P.L n) G) (xray (stepAt P K n) (xree P K n) H (Q n) Ñ (W (n*P.L)) x y)=abr (D n) (X n) x y:= whyPack P K Ñ H W Q n x y
  exact he.congr (Eventually.of_forall fun n=> congr_fun (hz n).symm r)
lemma seasonal {Z:Canvas G}{Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}(e:P.Branches K G)(h:LocalRatio Ñ)(p:∀ i r,Yields (fun n=>W n i r) (Z i r)) (F:PaintKit P K G H Q Γ M)(i r):
    Yields (fun n=>summer (stepAt P K n) (xree P K n) H (Q n) Ñ (W (n*P.L)) i r) (snow P K Ñ Γ M Z i r):= by
    let X (n:Side) j:= bend (weaveH (ratioN P.L n) G) (xray (stepAt P K n) (xree P K n) H (Q n) Ñ (W (n*P.L)) j i)
    have hv j : Yields (fun n=>X n j r) (spurs P K Ñ Γ M Z j i r) := spurs_enter P K Ñ H W Q e h p F j i r
    have he:=scoopY (parcelY (P:=X) (F:=fun j=>spurs P K Ñ Γ M Z j i) (s:=Finset.range (3+3*i)) (fun j _=>hv j))
    refine he.congr (Eventually.of_forall fun n=>?_); exact congr_fun (season_fold P K Ñ H W Q n i).symm _

lemma bay (P:Patch)(K:KernelChoices)(G:Gauge)(Ñ:ChartRatio G)(i r) : Yields (fun n=>uband (U:=Woods G n) (plugζ (stepAt P K n) Ñ) i r) (uband (U:=YForest G) (perζ K Ñ) i r):= by
  simp_rw [plug_site P K Ñ]; exact costY _ _ _
lemma raw_roll {Z:Canvas G}{Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}(e:P.Branches K G)(h:LocalRatio Ñ)(p:∀ i r,Yields (fun n=>W n i r) (Z i r)) (F:PaintKit P K G H Q Γ M)(hf : Pilots (fun n=>precisionC G n Y) (plain G Y))(i r):
      Yields (fun n=> winter (stepAt P K n) (xree P K n) H Y (Q n) Ñ (W (n*P.L)) i r) (tinge P K Ñ (plain G Y) Γ M Z i r):=
    ((flatY hf i r).sub (seasonal P K Ñ H W Q e h p F i r)).add (bay P K G Ñ i r)
end patch

section nominees
variable (A:Levels G)(N m:ℕ)
abbrev roam (A:Levels G) (N m:ℕ) (n:Side):= installed (mStep A n m).ratio (predictionA A N m)
lemma resin (h:m<N) : PaintKit (loose A m) A.clock.kernel G (freeForms A N (m+1)) (roam A N m) (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) := by
    obtain ⟨s,hs,H⟩:= schedule_flat A.clock.kernel G _ _ (A.clock.adm (m+1)) (A.clock.adm m); obtain ⟨b,hb,hB⟩:= H (loose A m) rfl (A.blocks m 0).branches
    have he := (hB A m rfl rfl rfl).actual N h
    have hc n: allotM (weaveFine (ratioN (loose A m).L n) G) (weaveFine (ratioN (loose A m).L n) G) (mer (G:=G) (loose A m) A.clock.kernel (freeForms A N (m+1)) n)=(conditional A N m).acts n:= (show _ from ((cond_laws A m N).2.2 n (n*(loose A m).L) rfl).symm)
    have hm n: allotM (weaveFine (ratioN (loose A m).L n) G) (Equiv.refl (Woods G n)) (teller G (loose A m) A.clock.kernel (roam A N m) n)=(feedA A N m).acts n:= (feed_period A N m h n (n*(loose A m).L) rfl).symm
    exact ⟨by simp_rw [hc]; exact matrix_visit he.1 hs hb.le,by simp_rw [hm]; exact matrix_visit he.2.1 hs hb.le⟩
lemma horizon_ports (j:ℕ) : Pilots (fun n=> precisionC G n (freeForms A N j)) (plain G (freeForms A N j)) := by
    obtain ⟨s,a,hp,ha,H⟩:= forms_tail A.clock.kernel.penalty A.clock.kernel.penalty_pos _ (A.clock.adm j); exact plain_fold _ ((H A j rfl rfl).1 N) hp ha.le
end nominees
end YM.WilsonCoeffUV.Bank
