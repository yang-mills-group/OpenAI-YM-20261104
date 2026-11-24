import YM.GradedFar.Floor
/-!
# Normalize link measurements on the common exterior list

Two-zone variable capacities. n+m programming includes also all-seven masks, spread work and
mixed horizon at relative radius. Casting conveniences for genuine array calls.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(P:ℝ→tower S)
variable {n m k h N N':ℕ} {d:Fin n→ℕ}{e:Fin m→ℕ}
local notation "d*"=> Fin.append d e
abbrev Sticker (G:Gauge):= (i:ℕ)×Sec G i
abbrev stickers (u:AppointedH140Inputs G d) (i:Fin n): Sticker G:= ⟨d i,u i⟩
private lemma taped (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e)(i:Fin (n+m)):
    
    ∃ w:Sec G (d* i), (⟨d* i,w⟩:Sticker G)=Fin.append (stickers u) (stickers v) i := by
    have W {j k:ℕ} (h:j=k)(u:Sec G k):∃ v:Sec G j,(⟨j,v⟩:Sticker G)=⟨k,u⟩:= by subst j; exact ⟨u,rfl⟩
    refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp only [Fin.append_left,Fin.append_right]
    · exact W (Fin.append_left ..) (u _)
    exact W (Fin.append_right ..) (v _)
def tape (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e):AppointedH140Inputs G d*:= fun i=> (taped u v i).choose
@[simp] lemma tape_bill (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e)(i:Fin (n+m)): stickers (tape u v) i= Fin.append (stickers u) (stickers v) i:= (taped u v i).choose_spec
lemma tape_box {U:ℝ}(hU:0≤U)(u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e)(hu:Box u U)(hv:Box v U): Box (tape u v) U:= by
 apply (boxes hU).2; intro i; let W (i:Sticker G):= width i.snd; change W (stickers (tape u v) i) ≤ _; rw [tape_bill]; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp only [Fin.append_left, Fin.append_right]
 · exact (boxes hU).1 hu _
 exact (boxes hU).1 hv _
lemma tape_horizon (hd:AppointedH140Through h d)(he:AppointedH140Through h e): AppointedH140Through h d*:= by
 intro i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp only [Fin.append_left, Fin.append_right]; exacts [hd i,he i]
-- translation/cast budget
local notation "r*"=> fun (r s:ℝ)=> Fin.append (fun _:Fin n=>r) (fun _:Fin m=>s)
def recite (r s:ℝ)(x:Positions n)(y:Positions m)(t:Lattice.Site (C.side N N'))(u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e): ℂ:= assemble F P (r* r s) d* N N' t (Fin.append x y) (tape u v)
lemma tape_names (r s:ℝ)(u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e): names F P (r* r s) (tape u v)= Fin.append (names F P (fun _=>r) u) (names F P (fun _=>s) v):= by
 let L (r:ℝ)(i:Sticker G):C.book.Token:=⟨_,call F P _ r i.snd⟩
 funext i; change L ((r* r s) i) (stickers (tape u v) i) = _; rw [tape_bill]; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> dsimp only <;> simp only [Fin.append_left,Fin.append_right] <;> rfl
lemma recites (r s:ℝ)(x:Positions n)(y:Positions m)(t:Lattice.Site (C.side N N'))(u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e):
    recite F P r s x y t u v=C.numeric N N' (Fin.append (names F P (fun _=>r) u) (names F P (fun _=>s) v))
    (Fin.append (fun i=> wrap _ (x i)+t) (fun i=> wrap _ (y i)+t)):=by
 unfold recite; rw [assembled,tape_names]; congr 1; funext i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp
-- center translation of continuum m_N identities keeps locations at fixed center; every viewer then by old program
lemma combo_today {r s T:ℝ}(u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e){x: Points n}{y:Points m}(hr:0<r)
    (hp:forest x (T•y)∈conf (n+m))(o:E4): nl P d* (r* r s) (r • forest x (T•y)) (tape u v) = today F P none o r (r * T) s x y u v:= by
 let z:=forest x (T•y); let W:=tape u v; let L (r:ℝ)(i:Sticker G): C.book.Token:= ⟨_,S.representative _ (assign P r _ i.snd)⟩; let L₁:=fun i=> assign P ((r* r s) i) (d* i) (W i); let l:= Orbits.names L₁
 have hL(i) : l i=L ((r* r s) i) (stickers W i):=rfl
 change S.classMoment (spectator F none) _ _ L₁=_; rw [today_apply,atTable (T':=spectator F none) d* _ (spectate F none) (Work.A05.smul_conf hr hp)]
 have hV : sites o r z=fun i=>(r•z) i+o:= funext fun i=>add_comm ..;
 have hT: Orbits.moment (spectator F none) (r • z).ofLp L₁= Orbits.moment (spectator F none) (sites o r z) L₁ := by rw [hV,carrying (spectate F none) (Work.A05.smul_conf hr hp)]
 rw [hT,Orbits.observed,whole_observed]; symm
 let Q: (Fin n ⊕ Fin m)≃ Fin (n+m):= finSumFinEquiv; apply Fork.renameRead Q (spectate F none).laws.toSymmetric (radius_conf hr o hp)
 · funext i; rcases i with i|i <;> simp [Q,z,sites,mul_smul]
 funext i; rcases i with i|i
 · change l (Q (Sum.inl i))=L r (stickers u i); rw [hL,tape_bill]; simp [Q]
 change l (Q (Sum.inr i))=L s (stickers v i); rw [hL,tape_bill]; simp [Q]

abbrev shiftFar (r s:ℝ)(u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e) : AppointedH140Inputs G d*:= fun i=> relative P r ((r* r s) i) (d* i) (tape u v i)
lemma assemble_shift (r s:ℝ)(u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e)(t:Lattice.Site (C.side N N'))(x:Positions (n+m)):
    assemble F P (fun _=>r) d* N N' t x (shiftFar P r s u v)=assemble F P (r* r s) d* N N' t x (tape u v):= by
 rw [assembled,assembled]; apply congrArg (fun z => C.numeric N N' z _); funext i; change (⟨d* i,constantSection F (d* i) (assign P r _ (relative P _ _ _ _))⟩:C.book.Token)=_; rw [atHome]; rfl
lemma nl_shift (r s:ℝ)(u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e)(x:Points (n+m)):
    nl P d* (fun _=>r) x (shiftFar P r s u v)=nl P d* (r* r s) x (tape u v):= by
 apply congrArg (S.classMoment S d* x); funext i; exact atHome ..
end YM.Integration.GradedFar.Auth
