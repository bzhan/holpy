<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#">geometry</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#">New</b-dropdown-item>
          <b-dropdown-item href="#">Open</b-dropdown-item>
          <b-dropdown-item href="#">Save</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item href="#" @click="handleClickSelect">Select</b-nav-item>
        <b-nav-item-dropdown text="Construct" left>
          <b-dropdown-item href="#" @click="handleClickConstructPoint">Point</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructLine">Line</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructCircle">Circle</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructIntersection">Intersection</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructMidpoint">Midpoint</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructPerpendicular">Perpendicular</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructParallel">Parallel</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Constraint" left>
          <b-dropdown-item href="#" @click="handleClickCongruentSegment">Congruent Segment</b-dropdown-item>
          <b-dropdown-item href="#">Equal Angle</b-dropdown-item>
          <b-dropdown-item href="#">Equal Ratio</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Prove" left>
          <b-dropdown-item href="#">Prove</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Help" left>
          <b-dropdown-item href='#'>Help</b-dropdown-item>
        </b-nav-item-dropdown>        
      </b-navbar-nav>
    </b-navbar>
    <div id="canvas" ref="p">
      <v-stage :config="stageSize" ref="stage" @click="handleClickLayer" @mousemove="handleMouseMove">
        <v-layer id="circleLayer" ref="circleLayer"></v-layer>
        <v-layer id="lineLayer" ref="lineLayer"></v-layer>
        <v-layer id="anchorLayer" ref="anchorLayer"></v-layer>

      </v-stage>
    </div>
    <div id="tool">
      <h6>Tool: {{status}}</h6>
    </div>

<!--    <div id="theory-list" v-show="ref_proof === undefined">-->
<!--      <Content v-if="filelist !== undefined"-->
<!--               v-bind:filelist="filelist"-->
<!--               v-on:select-theory="onSelectTheory"-->
<!--               ref="content"/>-->
<!--    </div>-->
<!--    <div id="proof-context" v-show="ref_proof !== undefined">-->
<!--      <ProofContext v-bind:ref_proof="ref_proof" ref="context"/>-->
<!--    </div>-->
<!--    <div id="theory-content">-->
<!--      <Theory v-bind:theory="theory"-->
<!--              v-bind:ref_status="ref_status"-->
<!--              v-bind:ref_context="ref_context"-->
<!--              :editor="editor"-->
<!--              v-on:set-message="onSetMessage"-->
<!--              v-on:set-proof="handle_set_proof"-->
<!--              v-on:query="handle_query"-->
<!--              v-on:goto-link="handleGoToLink"-->
<!--              ref="theory"/>-->
<!--    </div>-->
<!--    <div id="message" v-show="ref_proof === undefined">-->
<!--      <Message v-bind:message="message" ref="message"/>-->
<!--    </div>-->
<!--    <div id="status" v-show="ref_proof !== undefined && query === undefined">-->
<!--      <ProofStatus v-bind:ref_proof="ref_proof" ref="status"/>-->
<!--    </div>-->
<!--    <div id="query" v-show="ref_proof !== undefined && query !== undefined">-->
<!--      <ProofQuery v-bind:query="query"-->
<!--                  v-on:query-ok="handle_query_ok"-->
<!--                  v-on:query-cancel="handle_query_cancel"/>-->
<!--    </div>-->

  </div>
</template>

<script>
  import Vue from 'vue'
  import VueKonva from 'vue-konva'
  import Konva from 'konva'

  Vue.use(VueKonva)
  Vue.use(Konva)
  export default {
    name: 'Geometry',
    components: {
    },
    data() {
      return {
        stageSize: {
          width: null,
          height: null,
        },
        status: "select",
        points: [],
        lines: [],
        circles: [],
        midpoints: [],
        paras: [],
        perps: [],
        eqangles: [],
        eqratios: [],
        selected: [],
        watchingMouse: [],
        requirement: {
          "point": 1,
          "line": 2,
          "circle": 2,
          "intersection": 2,
          "midpoint": 2,
          "perpendicular": 2,
          "perpendicularPointToLine": 2,
          "perpendicularLineToLine": 3,
          "parallel": 2
        },
        pointType: {
          "free": 0,
          "semi": 1,
          "fixed": 2
        },
        pointColor: {
          0: "red",
          1: "green",
          2: "grey"
        }
      }
    },
    mounted() {
      this.matchSize()
    },
    created: function() {
      window.addEventListener("resize", this.matchSize)
    },
    methods: {
      matchSize() {
        this.stageSize.height = this.$refs.p.clientHeight - 10
        this.stageSize.width = this.$refs.p.clientWidth - 10
      },
      handleClickLayer() {
        let x = this.$refs.stage.getNode().getPointerPosition().x
        let y = this.$refs.stage.getNode().getPointerPosition().y
        let canAdd = true
        for (let id in this.lines) {
          const ps = this.getEndpointsByLineId(id)
          const pos1 = this.getCoordinateByPoint(ps[0])
          const pos2 = this.getCoordinateByPoint(ps[1])
          const minDist = this.getMinDistPointToSeg([x, y], pos1, pos2)[0]
          if (minDist < 5) {
            canAdd = false
            break
          }
        }
        if (canAdd) {
          for (let id in this.points) {
            const p = this.getPointById(id)
            const dist = this.getDistByPointPos([x, y], [p.x(), p.y()])
            if (dist < 10) {
              canAdd = false
              break
            }
          }
        }
        if (canAdd) {
          for (let id in this.circles) {
            const circle = this.getCircleByCircleId(id)
            const dist = this.getDistByPointPos([x, y], [circle.x(), circle.y()])
            if (Math.abs(dist - circle.radius()) < 10) {
              canAdd = false
              break
            }
          }
        }
        if (canAdd) {
          if (this.status === "select") {
            this.clearActivationAll()
          }
          else if (this.status === "point") {
            this.addPoint(x, y, false, this.pointType.free)
            this.clearActivationAll()
          }
          else if (this.status === "line") {
            if (this.checkSelectedPlace(0)) {
              let newId = this.addPoint(x, y, true, this.pointType.free)
              this.addToSelected(newId)
            }
            else if (this.checkSelectedPlace(1)) {
              let newId = this.addPoint(x, y, false, this.pointType.free)
              this.addToSelected(newId)
              this.addLine(this.selected[0], this.selected[1])
              this.clearActivationAll()
            }
          }
          else if (this.status === "perpendicular") {
            if (this.checkSelectedPlace(0)) {
              let newId = this.addPoint(x, y, true, this.pointType.free)
              this.addToSelected(newId)
            }
            else if (this.checkSelectedPlace(1) && this.getTypeById(this.selected[0]) === "line") {
              let newId = this.addPoint(x, y, true, this.pointType.free)
              this.addToSelected(newId)
            }
            else if (this.checkSelectedPlace(2)) {
              const line = this.getLineByLineId("perpLineNext")
              const endpoints = line.points()
              const p = this.getPedalCoordinatePointToSeg([x, y], [endpoints[0], endpoints[1]],
                      [endpoints[2], endpoints[3]])
              const newId = this.addPoint(p[0], p[1], false, this.pointType.semi)
              this.addLine(this.selected[1], newId)
              this.clearActivationAll()
            }

          }
          else if (this.status === "circle") {
            let newId = this.addPoint(x, y, true, this.pointType.free)
            this.addToSelected(newId)
            if (this.checkReachLength(this.status)) {
              this.addCircle(this.selected[0], this.selected[1])
              this.clearActivationAll()
            }
          }
          else if (this.status === "parallel") {
            if (this.checkSelectedPlace(1)) {
              let newId = this.addPoint(x, y, true, this.pointType.free)
              this.addToSelected(newId)
            }
            else if (this.checkSelectedPlace(2)) {
              const line = this.getLineByLineId("paraLineNext")
              const endpoints = line.points()
              const p = this.getPedalCoordinatePointToSeg([x, y], [endpoints[0], endpoints[1]],
                      [endpoints[2], endpoints[3]])
              const newId = this.addPoint(p[0], p[1], false, this.pointType.semi)
              this.addLine(this.selected[1], newId)
              this.clearActivationAll()
            }
          }
        }
      },
      checkHaveName(name) {
        for (let id in this.points) {
          if (name === this.points[id]['name']) {
            return true
          }
        }
        return false
      },
      checkSelectedPlace(place) {
        return place === this.selected.length
      },
      checkReachLength(type) {
        return this.requirement[type] === this.selected.length
      },
      parseIdToName(id) {
        if (parseInt(id / 26) === 0) {
          return String.fromCharCode(65 + id % 26)
        }
        else {
          return String.fromCharCode(65 + id % 26) + String(parseInt(id / 26))
        }
      },
      addLine(id1, id2) {
        const anchor1 = this.$refs.stage.getNode().findOne('#' + id1)
        const anchor2 = this.$refs.stage.getNode().findOne('#' + id2)
        const x1 = anchor1.x()
        const y1 = anchor1.y()
        const x2 = anchor2.x()
        const y2 = anchor2.y()
        let id = 500
        while (this.lines.hasOwnProperty(id)) {
          id += 1
        }
        let info
        if (x1 < x2) {
          info = {"points": [id1, id2], "activated": false}
        } else {info = {"points": [id2, id1], "activated": false}}
        this.lines[id] = info
        const newLine = new Konva.Line({
          points: [x1, y1, x2, y2],
          stroke: "grey",
          strokeWidth: 2,
          id: id.toString(),
        })
        newLine.on("mouseover", () => {
          document.body.style.cursor = 'pointer'
          newLine.strokeWidth(4)
          this.$refs.lineLayer.getNode().draw()
        })
        newLine.on("mouseout", () => {
          document.body.style.cursor = 'default'
          if (info.activated === false) {
            newLine.strokeWidth(2)
            this.$refs.lineLayer.getNode().draw()
          }
        })
        newLine.on("click", () => {
                  if (this.status === "select") {
                    if (info.activated === true) {
                      info.activated = false
                      newLine.strokeWidth(2)
                    } else {
                      info.activated = true
                      newLine.strokeWidth(4)
                    }
                  }
                  else if (this.status === "point") {
                    this.addClickPosToLine(id, false, this.pointType.semi)
                  }
                  else if (this.status === "line") {
                    const pointId = this.addClickPosToLine(id, true, this.pointType.semi)
                    this.addToSelected(pointId)
                    if (this.checkReachLength(this.status)) {
                      this.addLine(this.selected[0], this.selected[1])
                      this.clearActivationAll()
                    }
                  }
                  else if (this.status === "intersection") {
                    info.activated = true
                    newLine.strokeWidth(4)
                    this.addToSelected(id)
                    if (this.checkReachLength(this.status)) {
                      this.getIntersection(this.selected[0], this.selected[1])
                      this.clearActivationAll()
                    }
                  }
                  else if (this.status === "circle") {
                    const newPtId = this.addClickPosToLine(id, true)
                    if (newPtId) {
                      this.addToSelected(newPtId)
                    }
                    if (this.checkReachLength(this.status)) {
                      this.addCircle(this.selected[0], this.selected[1])
                      this.clearActivationAll()
                    }
                  }
                  else if (this.status === "parallel") {
                    if (this.checkSelectedPlace(0)) {
                      info.activated = true
                      newLine.strokeWidth(4)
                      this.addToSelected(id)
                    }
                    else if (this.checkSelectedPlace(1)) {
                      const paraLinePts = this.getLineByLineId("paraLine").points()
                      const l2ps = this.getEndpointsByLineId(id)
                      const intersectionPos = this.getIntersectionLines([paraLinePts[0], paraLinePts[1]], [paraLinePts[2], paraLinePts[3]],
                              this.getCoordinateByPoint(l2ps[0]), this.getCoordinateByPoint(l2ps[1]))
                      if (intersectionPos) {
                        const newPtId = this.addPoint(intersectionPos[0], intersectionPos[1], true, this.pointType.semi)
                        this.addPointToLine(newPtId, id)
                        this.addToSelected(newPtId)
                      }
                    }
                    else if (this.checkSelectedPlace(2)) {
                      const paraLinePts = this.getLineByLineId("paraLineNext").points()
                      const l2ps = this.getEndpointsByLineId(id)
                      const intersectionPos = this.getIntersectionLines([paraLinePts[0], paraLinePts[1]], [paraLinePts[2], paraLinePts[3]],
                              this.getCoordinateByPoint(l2ps[0]), this.getCoordinateByPoint(l2ps[1]))
                      if (intersectionPos) {
                        const newPtId = this.addPoint(intersectionPos[0], intersectionPos[1], false, this.pointType.fixed)
                        this.addPointToLine(newPtId, id)
                        this.addToSelected(newPtId)
                        this.addLine(this.selected[1], this.selected[2])
                        this.paras.push([this.getEndPointsIdByLineId(this.selected[0])[0], this.getEndPointsIdByLineId(this.selected[0])[1],
                          this.selected[1], this.selected[2]])
                        this.clearActivationAll()
                      }
                    }
                  }
                  else if (this.status === "perpendicular") {
                    if (this.checkSelectedPlace(0)) {
                      info.activated = true
                      newLine.strokeWidth(4)
                      this.addToSelected(id)
                    }
                    else if (this.checkSelectedPlace(1)) {
                      if (this.getTypeById(this.selected[0]) === "point") {
                        this.addToSelected(id)
                        const perpToId = this.selected[1]
                        if (!perpToId) {
                          this.clearActivationAll()
                          return
                        }
                        const endPointIds = this.getEndPointsIdByLineId(perpToId)
                        const footPos = this.getPedalCoordinatePointToSeg(this.getCoordinateByPointId(this.selected[0]),
                                this.getCoordinateByPointId(endPointIds[0]), this.getCoordinateByPointId(endPointIds[1]), true)
                        if (footPos[0] === Infinity) {
                          this.clearActivationAll()
                          return
                        }
                        const footId = this.addPoint(footPos[0], footPos[1], false, this.pointType.fixed)
                        const perpToLine = this.getLineByLineId(perpToId)
                        perpToLine.getAttr('points').push(footPos[0], footPos[1])
                        this.addPointToLineList(this.lines[perpToId], footId, footPos[0])
                        this.addLine(this.selected[0], footId)
                        this.perps.push([this.selected[0], footId, this.getEndPointsIdByLineId(this.selected[1])[0],
                          this.getEndPointsIdByLineId(this.selected[1])[1]])
                        this.clearActivationAll()
                      }
                      else {
                        const perpLinePts = this.getLineByLineId("perpLine").points()
                        const l2ps = this.getEndpointsByLineId(id)
                        const intersectionPos = this.getIntersectionLines([perpLinePts[0], perpLinePts[1]], [perpLinePts[2], perpLinePts[3]],
                                this.getCoordinateByPoint(l2ps[0]), this.getCoordinateByPoint(l2ps[1]))
                        if (intersectionPos) {
                          const newPtId = this.addPoint(intersectionPos[0], intersectionPos[1], true, this.pointType.semi)
                          this.addPointToLine(newPtId, id)
                          this.addToSelected(newPtId)
                        }
                      }
                    }
                    else if (this.checkSelectedPlace(2)) {
                      const perpLinePts = this.getLineByLineId("perpLineNext").points()
                      const l2ps = this.getEndpointsByLineId(id)
                      const intersectionPos = this.getIntersectionLines([perpLinePts[0], perpLinePts[1]], [perpLinePts[2], perpLinePts[3]],
                              this.getCoordinateByPoint(l2ps[0]), this.getCoordinateByPoint(l2ps[1]))
                      if (intersectionPos) {
                        const newPtId = this.addPoint(intersectionPos[0], intersectionPos[1], false, this.pointType.fixed)
                        this.addPointToLine(newPtId, id)
                        this.addToSelected(newPtId)
                        this.addLine(this.selected[1], this.selected[2])
                        this.perps.push([this.getEndPointsIdByLineId(this.selected[0])[0], this.getEndPointsIdByLineId(this.selected[0])[1],
                          this.selected[1], this.selected[2]])
                        this.clearActivationAll()
                      }
                    }
                  }
                }
          )
        this.$refs.lineLayer.getNode().add(newLine)
        this.$refs.lineLayer.getNode().draw()
      },
      addCircle(id1, id2, id3) {
        let radius
        let center
        let p1 = this.getPointById(id1)
        let p2 = this.getPointById(id2)
        let p3
        if (!id3) {
          center = p1
          radius = this.getDistByPointPos(this.getCoordinateByPoint(p1), this.getCoordinateByPoint(p2))
        }
        else {
          p3 = this.getPointById(id3)
        }
        let id = 1000
        while (this.circles.hasOwnProperty(id)) {
          id += 1
        }
        let info = undefined
        if (!p3) {
          info = {"points": [p1, p2], "activated": false}
        }
        this.circles[id] = info
        const newCircle = new Konva.Circle({
          radius: radius,
          x: center.x(),
          y: center.y(),
          stroke: "grey",
          strokeWidth: 2,
          id: id.toString(),
          fillEnabled: false
        })
        newCircle.on("mouseover", () => {
          document.body.style.cursor = 'pointer'
          newCircle.strokeWidth(4)
          this.draw(["circle"])
        })
        newCircle.on("mouseout", () => {
          document.body.style.cursor = 'default'
          if (info.activated === false) {
            newCircle.strokeWidth(2)
            this.draw(["circle"])
          }
        })
        newCircle.on("click", () => {
          if (this.status === "select") {
            if (info.activated === true) {
              info.activated = false
              newCircle.strokeWidth(2)
            } else {
              info.activated = true
              newCircle.strokeWidth(4)
            }
            this.draw(["circle"])
          }
          else if (this.status === "point") {
            this.addPointToCircleWithCheck(this.getMousePos(), id, false, this.pointType.semi)
            this.draw(["circle"])
          }
          else if (this.status === "line") {
            const pointId = this.addPointToCircleWithCheck(this.getMousePos(), id, true, this.pointType.semi)
            this.addToSelected(pointId)
            if (this.checkReachLength(this.status)) {
              this.addLine(this.selected[0], this.selected[1])
              this.clearActivationAll()
            }
          }
          else if (this.status === "intersection") {
            info.activated = true
            newCircle.strokeWidth(4)
            this.addToSelected(id)
            this.draw(["circle"])
            if (this.checkReachLength(this.status)) {
              this.getIntersection(this.selected[0], this.selected[1])
              this.clearActivationAll()
            }
          }
          else if (this.status === "parallel") {
            if (this.checkSelectedPlace(1)) {
              const line = this.getLineByLineId("paraLine")
              const circle = this.getCircleByCircleId(id)
              const endpointsPos = line.points()
              const intersectionPos = this.getIntersectionLineAndCircle([endpointsPos[0], endpointsPos[1]], [endpointsPos[2], endpointsPos[3]],
                      [circle.x(), circle.y()], circle.radius())
              if (intersectionPos.length === 1) {
                const newId = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], true, this.pointType.semi)
                this.addPointToCircle(newId, id)
                this.addToSelected(newId)
              }
              else if (intersectionPos.length === 2) {
                const dist1 = this.getDistByPointPos(intersectionPos[0], this.getMousePos())
                const dist2 = this.getDistByPointPos(intersectionPos[1], this.getMousePos())
                let newPtId
                if (dist1 < dist2) {
                  newPtId = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], true, this.pointType.semi)
                } else {
                  newPtId = this.addPoint(intersectionPos[1][0], intersectionPos[1][1], true, this.pointType.semi)
                }
                this.addPointToCircle(newPtId, id)
                this.addToSelected(newPtId)
              }
            }
            else if (this.checkSelectedPlace(2)) {
              const line = this.getLineByLineId("paraLineNext")
              const circle = this.getCircleByCircleId(id)
              const endpointsPos = line.points()
              const intersectionPos = this.getIntersectionLineAndCircle([endpointsPos[0], endpointsPos[1]], [endpointsPos[2], endpointsPos[3]],
                      [circle.x(), circle.y()], circle.radius())
              if (intersectionPos.length === 1) {
                const newId = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], false, this.pointType.fixed)
                this.addPointToCircle(newId, id)
                this.addToSelected(newId)
              }
              else if (intersectionPos.length === 2) {
                const dist1 = this.getDistByPointPos(intersectionPos[0], this.getMousePos())
                const dist2 = this.getDistByPointPos(intersectionPos[1], this.getMousePos())
                let newPtId
                if (dist1 < dist2) {
                  newPtId = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], false, this.pointType.fixed)
                } else {
                  newPtId = this.addPoint(intersectionPos[1][0], intersectionPos[1][1], false, this.pointType.fixed)
                }
                this.addPointToCircle(newPtId, id)
                this.addToSelected(newPtId)
              }
              this.addLine(this.selected[1], this.selected[2])
              this.paras.push([this.getEndPointsIdByLineId(this.selected[0])[0], this.getEndPointsIdByLineId(this.selected[0])[1],
                this.selected[1], this.selected[2]])
              this.clearActivationAll()
            }
          }
          else if (this.status === "perpendicular") {
            if (this.checkSelectedPlace(0)) {
              const newPtId = this.addPointToCircleWithCheck(this.getMousePos(), id, true, this.pointType.semi)
              this.addToSelected(newPtId)
            }
            else if (this.checkSelectedPlace(1)) {
              const line = this.getLineByLineId("perpLine")
              const circle = this.getCircleByCircleId(id)
              const endpointsPos = line.points()
              const intersectionPos = this.getIntersectionLineAndCircle([endpointsPos[0], endpointsPos[1]], [endpointsPos[2], endpointsPos[3]],
                      [circle.x(), circle.y()], circle.radius())
              if (intersectionPos.length === 1) {
                const newId = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], true, this.pointType.semi)
                this.addPointToCircle(newId, id)
                this.addToSelected(newId)
              }
              else if (intersectionPos.length === 2) {
                const dist1 = this.getDistByPointPos(intersectionPos[0], this.getMousePos())
                const dist2 = this.getDistByPointPos(intersectionPos[1], this.getMousePos())
                let newPtId
                if (dist1 < dist2) {
                  newPtId = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], true, this.pointType.semi)
                } else {
                  newPtId = this.addPoint(intersectionPos[1][0], intersectionPos[1][1], true, this.pointType.semi)
                }
                this.addPointToCircle(newPtId, id)
                this.addToSelected(newPtId)
              }
            }
            else if (this.checkSelectedPlace(2)) {
              const line = this.getLineByLineId("perpLineNext")
              const circle = this.getCircleByCircleId(id)
              const endpointsPos = line.points()
              const intersectionPos = this.getIntersectionLineAndCircle([endpointsPos[0], endpointsPos[1]], [endpointsPos[2], endpointsPos[3]],
                      [circle.x(), circle.y()], circle.radius())
              if (intersectionPos.length === 1) {
                const newId = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], false, this.pointType.fixed)
                this.addPointToCircle(newId, id)
                this.addToSelected(newId)
              }
              else if (intersectionPos.length === 2) {
                const dist1 = this.getDistByPointPos(intersectionPos[0], this.getMousePos())
                const dist2 = this.getDistByPointPos(intersectionPos[1], this.getMousePos())
                let newPtId
                if (dist1 < dist2) {
                  newPtId = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], false, this.pointType.fixed)
                } else {
                  newPtId = this.addPoint(intersectionPos[1][0], intersectionPos[1][1], false, this.pointType.fixed)
                }
                this.addPointToCircle(newPtId, id)
                this.addToSelected(newPtId)
              }
              this.addLine(this.selected[1], this.selected[2])
              this.perps.push([this.getEndPointsIdByLineId(this.selected[0])[0], this.getEndPointsIdByLineId(this.selected[0])[1],
                this.selected[1], this.selected[2]])
              this.clearActivationAll()
            }
          }
          this.draw()
        })
        this.$refs.circleLayer.getNode().add(newCircle)
        this.draw(["circle"])
        return id
      },
      addClickPosToLine(lineId, activated, type) {
        const newX = this.$refs.stage.getNode().getPointerPosition().x
        const newY = this.$refs.stage.getNode().getPointerPosition().y
        const endpoints = this.getEndpointsByLineId(lineId)
        const r = this.getMinDistPointToSeg([newX, newY], this.getCoordinateByPoint(endpoints[0]), this.getCoordinateByPoint(endpoints[1]))
        const minDist = r[0]
        const foot = r[1]
        if (minDist < 5) {
          const newPtId = this.addPoint(foot[0], foot[1], activated, type)
          this.addPointToLine(newPtId, lineId)
          return newPtId
        }
      },
      addPointToLine(pointId, lineId) {
        const line = this.getLineByLineId(lineId)
        const pos = this.getCoordinateByPointId(pointId)
        line.getAttr('points').push(pos[0], pos[1])
        this.addPointToLineList(this.lines[lineId], pointId, pos[0])
      },
      addPointToLineList(info, id, x) {
        const increase = this.points[info.points[0]].x < this.points[info.points[1]].x
        for (let i = 0; i < info.points.length; i ++) {
          if (increase) {
            if (x > this.points[info.points[i]].x) {
              info.points.splice(i + 1, 0, id)
              return 0
            }
          }
          else {
            if (x < this.points[info.points[i]].x) {
              info.points.splice(i + 1, 0, id)
              return 0
            }
          }
        }
        info.points.push(id)
      },
      addPointToCircleWithCheck(pointPos, circleId, activated, type) {
        const circle = this.getCircleByCircleId(circleId)
        const x = circle.x()
        const y = circle.y()
        const radius = circle.getAttr('radius')
        const dist = this.getDistByPointPos([x, y], this.getMousePos())
        if (Math.abs(radius - dist) < 2) {
          const intersections = this.getIntersectionLineAndCircle(pointPos, [x, y],[x, y], radius)
          if (intersections) {
            let newPtId
            if (intersections.length === 2) {
              let minDist
              let minPt
              if (this.getDistByPointPos(intersections[0], this.getMousePos()) < this.getDistByPointPos(intersections[1], this.getMousePos())) {
                minDist = this.getDistByPointPos(intersections[0], this.getMousePos())
                minPt = 0
              } else {
                minDist = this.getDistByPointPos(intersections[1], this.getMousePos())
                minPt = 1
              }
              if (minDist < 2) {
                newPtId = this.addPoint(intersections[minPt][0], intersections[minPt][1], activated)
              }
            }
            else {
              if (this.getDistByPointPos(intersections[0], [x, y]) < 2) {
                newPtId = this.addPoint(intersections[0][0], intersections[0][1], activated, type)
              }
            }
            this.addPointToCircle(newPtId, circleId)
            return newPtId
          }
        }
        return null
      },
      addPointToCircle(pointId, circleId) {
        this.addPointToCircleList(this.circles[circleId], pointId)
      },
      addPointToCircleList(info, id) {
        info.points.push(id)
      },
      getMousePos() {
        return [this.$refs.stage.getNode().getPointerPosition().x, this.$refs.stage.getNode().getPointerPosition().y]
      },
      getTypeById(s) {
        let id
        if (typeof s === "string") {
          if (s.indexOf("Line") !== -1) {
            return "line"
          }
          else if (s.indexOf("Point") !== -1) {
            return "point"
          }
          else if (s.indexOf("Circle") !== -1) {
            return "circle"
          }
          else {
            id = parseInt(s)
          }
        }
        else if (typeof s === "number") {
          id = s
        }
        else {
          return
        }
        if (id >= 0 && id < 500) {
          return "point"
        }
        else if (id >= 500 && id < 1000) {
          return "line"
        }
        else if (id >= 1000) {
          return "circle"
        }
        return null
      },
      getYByLineId(lineId, newX) {
        const endpoints = this.getEndpointsByLineId(lineId)
        const p1 = this.getCoordinateByPoint(endpoints[0])
        const p2 = this.getCoordinateByPoint(endpoints[1])
        return this.getYbyLinePos(p1[0], p1[1], p2[0], p2[1], newX)
      },
      getXByLineId(lineId, newY) {
        const endpoints = this.getEndpointsByLineId(lineId)
        const p1 = this.getCoordinateByPoint(endpoints[0])
        const p2 = this.getCoordinateByPoint(endpoints[1])
        return this.getXbyLinePos(p1[0], p1[1], p2[0], p2[1], newY)
      },
      getYbyLinePos(x1, y1, x2, y2, newX) {
        return y1 + ((y2 - y1) / (x2 - x1)) * (newX - x1)
      },
      getXbyLinePos(x1, y1, x2, y2, newY) {
        return (newY - y1) / ((y2 - y1) / (x2 - x1)) + x1
      },
      getLineByLineId(id) {
        return this.$refs.lineLayer.getNode().findOne('#' + id)
      },
      getCircleByCircleId(id) {
        return this.$refs.circleLayer.getNode().findOne('#' + id)
      },
      getLineIdByPointId(id1, id2) {
        for (let id in this.lines) {
          if (this.lines[id].points.indexOf(id1) !== -1 && this.lines[id].points.indexOf(id2) !== -1) {
            return id
          }
        }
        return null
      },
      getEndPointsIdByLineId(id) {
        return [this.lines[id].points[0], this.lines[id].points[this.lines[id].points.length - 1]]
      },
      getEndpointsByLineId(id) {
        const ids = this.getEndPointsIdByLineId(id)
        const p1 = this.$refs.anchorLayer.getNode().findOne('#' + ids[0])
        const p2 = this.$refs.anchorLayer.getNode().findOne('#' + ids[1])
        return [p1, p2]
      },
      getCoordinateByPoint(p) {
        return [p.x(), p.y()]
      },
      getCoordinateByPointId(id) {
        return this.getCoordinateByPoint(this.getPointById(id))
      },
      getCenterByCircle(c) {
        return [c.x(), c.y()]
      },
      getRadiusByCircle(c) {
        return c.radius()
      },
      getPointById(id) {
        return this.$refs.anchorLayer.getNode().findOne('#' + id)
      },
      getShiftedExtendLinePos(group1, group2, target) {
        const x1 = group1[0]
        const y1 = group1[1]
        const x2 = group2[0]
        const y2 = group2[1]
        const x = target[0]
        const y = target[1]
        const k = (y2 - y1) / (x2 - x1)
        const b = y - k * x
        return [[-10000, k * -10000 + b], [10000, k * 10000 + b]]
      },
      getRotatedByPos(id) {
        return this.getCoordinateByPoint(this.getPointById(id))
      },
      getRotatedPointPos(group1, group2, angle) {
        const x = group1[0]
        const y = group1[1]
        const cx = group2[0]
        const cy = group2[1]
        const radians = (Math.PI / 180) * angle
        const cos = Math.cos(radians)
        const sin = Math.sin(radians)
        return [(cos * (x - cx)) + (sin * (y - cy)) + cx, (cos * (y - cy)) - (sin * (x - cx)) + cy]
      },
      getRotatedPointPosById(id1, id2, angle) {
        const p1 = this.getPointById(id1)
        const p2 = this.getPointById(id2)
        return this.getRotatedPointPos(this.getCoordinateByPoint(p1), this.getCoordinateByPoint(p2), angle)
      },
      rotatePoint(id1, id2, angle) {
        this.updatePointPos(id1, this.getRotatedPointPosById(id1, id2, angle))
      },
      getRotatedPointOnLinePosById(lineId, pointId, angle) {
        let newPoints = []
        for (let i in this.lines[lineId].points) {
          newPoints = newPoints.concat(this.getRotatedPointPosById(this.lines[lineId].points[i], pointId, angle))
        }
        return newPoints
      },
      rotateLine(lineId, pointId, angle) {
        for (let i in this.lines[lineId].points) {
          this.rotatePoint(this.lines[lineId].points[i], pointId, angle)
        }
        this.updateLine(lineId)
      },
      getExtendPos(group1, group2) {
        return [[-10000, this.getYbyLinePos(group1[0], group1[1], group2[0], group2[1], -10000)],
          [10000, this.getYbyLinePos(group1[0], group1[1], group2[0], group2[1], 10000)]]
      },
      checkIsLeft(group1, group2, group) {
        return ((group2[0] - group1[0]) * (group[1] - group1[1]) - (group2[1] - group1[1]) * (group[0] - group1[0])) > 0
      },
      getIntersection(id1, id2) {
        const type1 = this.getTypeById(id1)
        const type2 = this.getTypeById(id2)
        if (type1 === "line" && type2 === "line") {
          const l1ps = this.getEndpointsByLineId(this.selected[0])
          const l2ps = this.getEndpointsByLineId(this.selected[1])
          const intersectionPos = this.getIntersectionLines(this.getCoordinateByPoint(l1ps[0]), this.getCoordinateByPoint(l1ps[1]),
                  this.getCoordinateByPoint(l2ps[0]), this.getCoordinateByPoint(l2ps[1]))
          if (intersectionPos) {
            const newPtId = this.addPoint(intersectionPos[0], intersectionPos[1], false, this.pointType.fixed)
            this.addPointToLine(newPtId, this.selected[0])
            this.addPointToLine(newPtId, this.selected[1])
            return [newPtId]
          }
        }
        else if ((type1 === "line" && type2 === "circle") || (type1 === "circle" && type2 === "line")) {
          const lineId = type1 === "line" ? id1 : id2
          const circleId = type1 === "line" ? id2 : id1
          const endpoints = this.getEndpointsByLineId(lineId)
          const circle = this.getCircleByCircleId(circleId)
          const intersectionPos = this.getIntersectionLineAndCircle(this.getCoordinateByPoint(endpoints[0]), this.getCoordinateByPoint(endpoints[1]),
          [circle.x(), circle.y()], circle.radius())
          if (intersectionPos.length >= 1) {
            const newPtId1 = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], false, this.pointType.fixed)
            this.addPointToCircle(newPtId1, circleId)
            this.addPointToLine(newPtId1, lineId)
            if (intersectionPos.length === 2) {
              const newPtId2 = this.addPoint(intersectionPos[1][0], intersectionPos[1][1], false, this.pointType.fixed)
              this.addPointToCircle(newPtId2, circleId)
              this.addPointToLine(newPtId2, lineId)
              return [newPtId1, newPtId2]
            }
            return [newPtId1]
          }
        }
        else if (type1 === "circle" && type2 === "circle") {
          const circle1 = this.getCircleByCircleId(id1)
          const circle2 = this.getCircleByCircleId(id2)
          const intersectionPos = this.getIntersectionCircles(this.getCenterByCircle(circle1), this.getRadiusByCircle(circle1),
          this.getCenterByCircle(circle2), this.getRadiusByCircle(circle2))
          if (intersectionPos) {
            const newPtId1 = this.addPoint(intersectionPos[0][0], intersectionPos[0][1], false, this.pointType.fixed)
            this.addPointToCircle(newPtId1, id1)
            this.addPointToCircle(newPtId1, id2)
            if (intersectionPos.length === 2) {
              const newPtId2 = this.addPoint(intersectionPos[1][0], intersectionPos[1][1], false, this.pointType.fixed)
              this.addPointToCircle(newPtId2, id1)
              this.addPointToCircle(newPtId2, id2)
              return [newPtId1, newPtId2]
            }
            return [newPtId1]
          }
        }
      },
      getIntersectionLines(pair1, pair2, pair3, pair4) {
        const xa = pair1[0]
        const ya = pair1[1]
        const xb = pair2[0]
        const yb = pair2[1]
        const xc = pair3[0]
        const yc = pair3[1]
        const xd = pair4[0]
        const yd = pair4[1]
        let denominator = (yb - ya) * (xd - xc) - (xa - xb) * (yc - yd)
        if (denominator === 0) {
          return false
        }
        let x = ( (xb - xa) * (xd - xc) * (yc - ya)
                + (yb - ya) * (xd - xc) * xa
                - (yd - yc) * (xb - xa) * xc) / denominator
        let y = -( (yb - ya) * (yd - yc) * (xc - xa)
                + (xb - xa) * (yd - yc) * ya
                - (xd - xc) * (yb - ya) * yc) / denominator
        return [x, y]
      },
      getIntersectionCircles(pair1, r0, pair2, r1) {
        let x0 = pair1[0]
        let y0 = pair1[1]
        let x1 = pair2[0]
        let y1 = pair2[1]
        let a, dx, dy, d, h, rx, ry
        let x2, y2

        /* dx and dy are the vertical and horizontal distances between
         * the circle centers.
         */
        dx = x1 - x0
        dy = y1 - y0

        /* Determine the straight-line distance between the centers. */
        d = Math.sqrt((dy*dy) + (dx*dx))

        /* Check for solvability. */
        if (d > (r0 + r1)) {
          /* no solution. circles do not intersect. */
          return false
        }
        if (d < Math.abs(r0 - r1)) {
          /* no solution. one circle is contained in the other */
          return false
        }

        /* 'point 2' is the point where the line through the circle
         * intersection points crosses the line between the circle
         * centers.
         */

        /* Determine the distance from point 0 to point 2. */
        a = ((r0*r0) - (r1*r1) + (d*d)) / (2.0 * d)

        /* Determine the coordinates of point 2. */
        x2 = x0 + (dx * a/d)
        y2 = y0 + (dy * a/d)

        /* Determine the distance from point 2 to either of the
         * intersection points.
         */
        h = Math.sqrt((r0*r0) - (a*a))

        /* Now determine the offsets of the intersection points from
         * point 2.
         */
        rx = -dy * (h/d)
        ry = dx * (h/d)

        if (rx === 0) {
          return [[x2, y2]]
        }

        /* Determine the absolute intersection points. */
        let xi = x2 + rx
        let xi_prime = x2 - rx
        let yi = y2 + ry
        let yi_prime = y2 - ry

        return [[xi, yi], [xi_prime, yi_prime]]
      },
      getIntersectionLineAndCircle(lineEndpoint1, lineEndpoint2, centerPos, radius) {
        const r = radius
        const h = centerPos[0]
        const k = centerPos[1]
        const m = (lineEndpoint2[1] - lineEndpoint1[1]) / (lineEndpoint2[0] - lineEndpoint1[0])
        const n = lineEndpoint1[1] - m * lineEndpoint1[0]
        let a = 1 + m * m
        let b = - h * 2 + (m * (n - k)) * 2
        let c = h * h + (n - k) * (n - k) - r * r
        // get discriminant
        let d = b * b - 4 * a * c
        if (d >= 0) {
          // insert into quadratic formula
          let intersections = [
            (-b + Math.sqrt(b * b - 4 * a * c)) / (2 * a),
            (-b - Math.sqrt(b * b - 4 * a * c)) / (2 * a)
          ]
          if (d === 0) {
            // only 1 intersection
            return [[intersections[0], m * intersections[0] + n]]
          }
          return [[intersections[0], m * intersections[0] + n], [intersections[1], m * intersections[1] + n]]
        }
        // no intersection
        return []
      },
      getDistByPointId(id1, id2) {
        const e1 = this.getEndpointsByLineId(id1)
        const e2 = this.getEndpointsByLineId(id2)
        return this.getDistByPointPos(this.getCoordinateByPoint(e1[0]), this.getCoordinateByPoint(e1[1]),
        this.getCoordinateByPoint(e2[0]), this.getCoordinateByPoint(e2[1]))
      },
      getDistByPointPos(pair1, pair2) {
        const x1 = pair1[0]
        const y1 = pair1[1]
        const x2 = pair2[0]
        const y2 = pair2[1]
        return Math.sqrt(Math.pow((x2 - x1), 2) + Math.pow((y2 - y1), 2))
      },
      getPedalCoordinatePointToSeg(pair, pair1, pair2, extend) {
        if (!extend) {
          extend = true
        }
        const x = pair[0]
        const y = pair[1]
        const x1 = pair1[0]
        const y1 = pair1[1]
        const x2 = pair2[0]
        const y2 = pair2[1]
        const A = x - x1
        const B = y - y1
        const C = x2 - x1
        const D = y2 - y1
        const dot = A * C + B * D
        const len_sq = C * C + D * D
        let param = -1
        if (len_sq !== 0) {
          param = dot / len_sq
        }
        if (!extend && param < 0) {
          return [x1, y1]
        }
        if (!extend && param > 1) {
          return [x2, y2]
        }
        return [x1 + param * C, y1 + param * D]
      },
      getMinDistPointToSeg(pair, pair1, pair2) {
        const x = pair[0]
        const y = pair[1]
        const pedalPos = this.getPedalCoordinatePointToSeg(pair, pair1, pair2)
        const dx = x - pedalPos[0]
        const dy = y - pedalPos[1]
        return [Math.sqrt(dx * dx + dy * dy), pedalPos];
      },
      addPoint(x, y, activated, type) {
        let id = 0
        while (this.points.hasOwnProperty(id)) {
          id += 1
        }
        let name = this.parseIdToName(id)
        let t_id = id
        while (this.checkHaveName(name)) {
          t_id += 1
          name = this.parseIdToName(t_id)
        }
        let info = undefined
        if (activated) {
          info = {"name": name, "activated": true, "x": x, "y": y, "type": type}
        } else {
          info = {"name": name, "activated": false, "x": x, "y": y, "type": type}
        }
        this.points[id] = info
        const group = new Konva.Group({
          x: x,
          y: y,
          draggable: true,
          isDragging: false,
          id: id.toString()
        });
        let strokeWidth = 2
        if (activated) {
          strokeWidth = 4
        }
        const newCircle = new Konva.Circle({
          radius: 5,
          stroke: "black",
          strokeWidth: strokeWidth,
          fill: this.pointColor[type],
        })
        const newText = new Konva.Text({
          x: 5,
          y: -20,
          text: name,
          fontSize: 16
        })
        group.add(newCircle)
        group.add(newText)
        group.on("mouseover", () => {
          document.body.style.cursor = 'pointer'
          newCircle.strokeWidth(4)
          this.$refs.anchorLayer.getNode().draw()
        })
        group.on("mouseout", () => {
          document.body.style.cursor = 'default'
          if (info.activated === false) {
            newCircle.strokeWidth(2)
            this.$refs.anchorLayer.getNode().draw()
          }
        })
        group.on("click", () => {
          if (this.status === "select") {
            if (info.activated === true) {
              info.activated = false
              newCircle.strokeWidth(2)
            } else {
              info.activated = true
              newCircle.strokeWidth(4)
            }
            this.$refs.anchorLayer.getNode().draw()
          }
          else if (this.status === "line") {
            info.activated = true
            this.addToSelected(id)
            if (this.checkReachLength(this.status)) {
              this.addLine(this.selected[0], this.selected[1])
              this.clearActivationAll()
            }
          }
          else if (this.status === "midpoint") {
            info.activated = true
            this.addToSelected(id)
            if (this.checkReachLength(this.status)) {
              const lineId = this.getLineIdByPointId(this.selected[0], this.selected[1])
              if (lineId) {
                const p1 = this.$refs.anchorLayer.getNode().findOne(
                        '#' + this.selected[0])
                const p2 = this.$refs.anchorLayer.getNode().findOne(
                        '#' + this.selected[1])
                let calX = (p1.x() + p2.x()) / 2
                let calY = this.getYbyLinePos(p1.x(), p1.y(), p2.x(), p2.y(), calX)
                const newPtId = this.addPoint(calX, calY, false, this.pointType.semi)
                this.addPointToLine(newPtId, lineId)
                this.midpoints.push(newPtId, this.selected[0], this.selected[1])
            }
              this.clearActivationAll()
            }
          }
          else if (this.status === "perpendicular") {
            if (this.checkSelectedPlace(0) || (this.checkSelectedPlace(1) &&
                    this.getTypeById(this.selected[0]) === "line")) {
              info.activated = true
              this.addToSelected(id)
            }
          }
          else if (this.status === "parallel") {
            if (this.checkSelectedPlace(1)) {
              info.activated = true
              this.addToSelected(id)
            }
          }
          else if (this.status === "circle") {
            info.activated = true
            this.addToSelected(id)
            if (this.selected.length === 2) {
              this.addCircle(this.selected[0], this.selected[1])
              this.clearActivationAll()
            }
          }
        })
        group.on("dragmove", () => {
          this.updateFollow(id)
          this.updateObjects()
        })
        // group.on("dragend", this.handleDragEndAnchor)
        this.$refs.anchorLayer.getNode().add(group)
        this.draw()
        return id
      },
      addToSelected(id) {
        this.selected.push(id)
      },
      handleClickSelect() {
        this.status = "select"
      },
      handleClickConstructPoint() {
        this.status = "point"
      },
      handleClickConstructMidpoint() {
        this.status = "midpoint"
      },
      handleClickConstructLine() {
        this.status = "line"
      },
      handleClickConstructCircle() {
        this.status = "circle"
      },
      handleClickConstructPerpendicular() {
        this.status = "perpendicular"
      },
      handleClickConstructIntersection() {
        this.status = "intersection"
      },
      handleClickConstructParallel() {
        this.status = "parallel"
      },
      handleClickCongruentSegment() {
        this.status = "cong"
      },
      // updateDraggable() {
      //   for (let id in this.points) {
      //     this.getPointById(id).draggable(true)
      //   }
      //   for (let id in this.lines) {
      //     for (let i = 1; i < this.lines[id].points.length - 1; i ++) {
      //       window.console.log(this.points[this.lines[id].points[i]].name)
      //       this.getPointById(this.lines[id].points[i]).draggable(false)
      //     }
      //   }
      // },
      updateFollow(ptId) {
        let beforeX = this.points[ptId].x
        let beforeY = this.points[ptId].y
        let endpoint = this.getPointById(ptId)
        let isEndpoint = true
        let hasPointLinesId = []
        for (let lineId in this.lines) {
          let points = this.lines[lineId].points
          if (points.indexOf(parseInt(ptId)) === 0 || points.indexOf(parseInt(ptId)) === points.length - 1) {
            let anotherEndpointX = points.indexOf(parseInt(ptId)) === 0 ? this.getPointById(points[points.length - 1]).x() : this.getPointById(points[0]).x()
            let anotherEndpointY = points.indexOf(parseInt(ptId)) === 0 ? this.getPointById(points[points.length - 1]).y() : this.getPointById(points[0]).y()
            if (points.length > 2) {
              for (let i = 1; i < points.length - 1; i ++) {
                let betweenX = this.getPointById(points[i]).x()
                let betweenY = this.getPointById(points[i]).y()
                let ratio
                let otherNewX
                let otherNewY
                if (endpoint.x() === anotherEndpointX || beforeX === anotherEndpointX) {
                  ratio = (betweenY - beforeY) / (anotherEndpointY - beforeY)
                  otherNewY = (anotherEndpointY - endpoint.y()) * ratio + endpoint.y()
                  otherNewX = this.getXbyLinePos(endpoint.x(), endpoint.y(), anotherEndpointX, anotherEndpointY, otherNewY)
                }
                else {
                  ratio = (betweenX - beforeX) / (anotherEndpointX - beforeX)
                  otherNewX = (anotherEndpointX - endpoint.x()) * ratio + endpoint.x()
                  otherNewY = this.getYbyLinePos(endpoint.x(), endpoint.y(), anotherEndpointX, anotherEndpointY, otherNewX)
                }
                this.points[ptId].x = endpoint.x()
                this.points[ptId].y = endpoint.y()
                this.getPointById(points[i]).x(otherNewX)
                this.getPointById(points[i]).y(otherNewY)
                this.$refs.anchorLayer.getNode().draw()
                this.updateFollow(points[i], false)
              }
            }
          }
          else {
            isEndpoint = false
            if (points.indexOf(parseInt(ptId)) !== -1) {
              hasPointLinesId.push(lineId)
            }
          }
        }
        if (!isEndpoint) {
          if (hasPointLinesId.length === 1) {
            let minDist = Infinity
            let minPos
            hasPointLinesId.forEach(id => {
              let endpoints = this.getEndpointsByLineId(id)
              let r = this.getMinDistPointToSeg([endpoint.x(), endpoint.y()],
                      this.getCoordinateByPoint(endpoints[0]), this.getCoordinateByPoint(endpoints[1]), true)
              minDist = r[0] < minDist ? r[0] : minDist
              minPos = r[0] === minDist ? r[1] : minPos
            })
            this.getPointById(ptId).x(minPos[0])
            this.getPointById(ptId).y(minPos[1])
          }
        }
      },
      updatePointPos(id, newPos) {
        const p = this.getPointById(id)
        p.x(newPos[0])
        p.y(newPos[1])
        this.points[id].x = newPos[0]
        this.points[id].y = newPos[1]
      },
      updateLine(id) {
        let newPoints = []
        for (let i = 0; i < this.lines[id].points.length; i ++) {
          newPoints = newPoints.concat(this.getCoordinateByPointId(this.lines[id].points[i]))
        }
        this.getLineByLineId(id).points(newPoints)
      },
      updateObjects() {
        for (let id in this.lines) {
          this.updateLine(id)
          // for (let i = 0; i < this.lines[id].points.length; i ++) {
          //   new_points = new_points.concat(this.getCoordinateByPointId(this.lines[id].points[i]))
          // }
          // this.getLineByLineId(id).points(new_points)
        }
        this.draw()
      },
      draw(layers) {
        if (!layers) {
          this.$refs.anchorLayer.getNode().draw()
          this.$refs.lineLayer.getNode().draw()
          this.$refs.circleLayer.getNode().draw()
          return
        }
        if (layers.indexOf("point") !== -1) {
          this.$refs.anchorLayer.getNode().draw()
        }
        if (layers.indexOf("line") !== -1) {
          this.$refs.lineLayer.getNode().draw()
        }
        if (layers.indexOf("circle") !== -1) {
          this.$refs.circleLayer.getNode().draw()
        }
      },
      clearActivationAll() {
        this.selected = []
        let allPoints = this.$refs.anchorLayer.getNode().getChildren()
        let allLines = this.$refs.lineLayer.getNode().getChildren()
        let allCircles = this.$refs.circleLayer.getNode().getChildren()
        for (let i = 0; i < allPoints.length; i ++) {
          allPoints[i].getChildren()[0].strokeWidth(2)
        }
        for (let i = 0; i < allLines.length; i ++) {
          allLines[i].strokeWidth(2)
        }
        for (let i = 0; i < allCircles.length; i ++) {
          allCircles[i].strokeWidth(2)
        }
        for (let id in this.points) {
          this.points[id]['activated'] = false
        }
        for (let id in this.lines) {
          this.lines[id]['activated'] = false
        }
        for (let id in this.circles) {
          this.circles[id]['activated'] = false
        }
        this.draw()
      },
      handleMouseMove() {
        if (this.watchingMouse) {
          const mousePos = this.getMousePos()
          if (this.watchingMouse.indexOf("mouseLine") !== -1) {
            const line = this.getLineByLineId("mouseLine")
            if (line) {
              line.points([line.points()[0], line.points()[1], mousePos[0] - 1, mousePos[1] - 1])
            }
          }
          if (this.watchingMouse.indexOf("paraLine") !== -1) {
            const line = this.getLineByLineId("paraLine")
            const mousePos = this.getMousePos()
            if (line) {
              const p = this.getShiftedExtendLinePos([line.points()[0], line.points()[1]],
                      [line.points()[2], line.points()[3]], mousePos)
              const extended = this.getExtendPos(p[0], mousePos)
              line.points([extended[0][0], extended[0][1], extended[1][0], extended[1][1]])
            }
          }
          if (this.watchingMouse.indexOf("paraLineNext") !== -1) {
            const line = this.getLineByLineId("paraLineNext")
            if (line) {
              const endpoints = line.points()
              const p = this.getPedalCoordinatePointToSeg(this.getMousePos(), [endpoints[0], endpoints[1]], [endpoints[2], endpoints[3]])
              line.points([p[0], p[1], this.getCoordinateByPointId(this.selected[1])[0], this.getCoordinateByPointId(this.selected[1])[1]])
            }
          }
          if (this.watchingMouse.indexOf("perpLine") !== -1) {
            const line = this.getLineByLineId("perpLine")
            if (line) {
              const endpoints = this.getEndpointsByLineId(this.selected[0])
              const p = this.getPedalCoordinatePointToSeg(mousePos, this.getCoordinateByPoint(endpoints[0]), this.getCoordinateByPoint(endpoints[1]))
              const p1 = this.getRotatedPointPos(this.getCoordinateByPoint(endpoints[0]), p, 90)
              const p2 = this.getRotatedPointPos(this.getCoordinateByPoint(endpoints[1]), p, 90)
              const extended = this.getExtendPos(p1, p2)
              line.points([extended[0][0], extended[0][1], extended[1][0], extended[1][1]])
            }
          }
          if (this.watchingMouse.indexOf("perpLineNext") !== -1) {
            const line = this.getLineByLineId("perpLineNext")
            if (line) {
              const endpoints = line.points()
              const p = this.getPedalCoordinatePointToSeg(mousePos, [endpoints[0], endpoints[1]], [endpoints[2], endpoints[3]])
              if (line.points().indexOf(-10000) !== -1) {
                line.points([p[0], p[1], line.points()[2], line.points()[3]])
              } else {
                line.points([line.points()[0], line.points()[1], p[0], p[1]])
              }
            }
          }

          if (this.watchingMouse.indexOf("mouseCircle") !== -1) {
            const circle = this.getCircleByCircleId("mouseCircle")
            if (circle) {
              circle.radius(this.getDistByPointPos([circle.x(), circle.y()], mousePos))
            }
          }
          this.draw()
        }
      }
    },
    watch: {
      status() {
        this.clearActivationAll()
      },
      selected() {
        this.watchingMouse = []

        if (this.selected.length === 1 && ["line", "circle", "perpendicular"].indexOf(this.status) !== -1) {
          const mousePos = this.getMousePos()
          let points, id
          if (this.status === "perpendicular" && this.getTypeById(this.selected[0]) === "line") {
            id = "perpLine"
            const endpoints = this.getEndPointsIdByLineId(this.selected[0])
            const p1 = this.getRotatedPointPos(this.getCoordinateByPointId(endpoints[0]), mousePos, 90)
            const p2 = this.getRotatedPointPos(this.getCoordinateByPointId(endpoints[1]), mousePos, 90)
            const extended = this.getExtendPos(p1, p2)
            points = [extended[0][0], extended[0][1], extended[1][0], extended[1][1]]
          }
          else {
            id = "mouseLine"
            const p = this.getCoordinateByPointId(this.selected[0])
            points = [p[0], p[1], mousePos[0], mousePos[1]]
          }
          const newLine = new Konva.Line({
            points: points,
            stroke: "grey",
            strokeWidth: 2,
            id: id
          })
          this.watchingMouse.push(id)
          this.$refs.lineLayer.getNode().add(newLine)
        } else {
          let line
          line = this.getLineByLineId("mouseLine")
          if (line) {
            line.remove()
          }
          line = this.getLineByLineId("perpLine")
          if (line) {
            line.remove()
          }
        }
        if (this.selected.length === 2 && ["perpendicular"].indexOf(this.status) !== -1
                && this.getTypeById(this.selected[1]) === "point") {
          const mousePos = this.getMousePos()
          const endpoints = this.getEndpointsByLineId(this.selected[0])
          const p1 = this.getRotatedPointPos(this.getCoordinateByPoint(endpoints[0]), mousePos, 90)
          const p2 = this.getRotatedPointPos(this.getCoordinateByPoint(endpoints[1]), mousePos, 90)
          const extended = this.getExtendPos(p1, p2)
          let points
          if (this.checkIsLeft(this.getCoordinateByPoint(endpoints[0]), this.getCoordinateByPoint(endpoints[1]),
          this.getCoordinateByPointId(this.selected[1]))) {
            points = [this.getCoordinateByPointId(this.selected[1])[0], this.getCoordinateByPointId(this.selected[1])[1],
              extended[1][0], extended[1][1]]
          }
          else {
            points = [extended[0][0], extended[0][1], this.getCoordinateByPointId(this.selected[1])[0],
              this.getCoordinateByPointId(this.selected[1])[1]]
          }
          const newLine = new Konva.Line({
            points: points,
            stroke: "grey",
            strokeWidth: 2,
            id: "perpLineNext"
          })
          this.watchingMouse.push("perpLineNext")
          this.$refs.lineLayer.getNode().add(newLine)
          const line = this.getLineByLineId("perpLine")
          if (line) {
            line.remove()
          }
        } else {
          const line = this.getLineByLineId("perpLineNext")
          if (line) {
            line.remove()
          }
        }

        if (this.selected.length === 1 && ["parallel"].indexOf(this.status) !== -1) {
          const endpoints = this.getEndpointsByLineId(this.selected[0])
          const points = this.getShiftedExtendLinePos(this.getCoordinateByPoint(endpoints[0]),
                  this.getCoordinateByPoint(endpoints[1]), this.getMousePos())
          const newLine = new Konva.Line({
            points: [points[0][0], points[0][1], points[1][0], points[1][1]],
            stroke: "grey",
            strokeWidth: 2,
            id: "paraLine"
          })
          this.watchingMouse.push("paraLine")
          this.$refs.lineLayer.getNode().add(newLine)
        }
        else {
          const line = this.getLineByLineId("paraLine")
          if (line) {
            line.remove()
          }
        }

        if (this.selected.length === 2 && ["parallel"].indexOf(this.status) !== -1) {
          const mousePos = this.getMousePos()
          const endpoints = this.getEndpointsByLineId(this.selected[0])
          const extended = this.getShiftedExtendLinePos(this.getCoordinateByPoint(endpoints[0]),
                  this.getCoordinateByPoint(endpoints[1]), mousePos)
          const s = this.getCoordinateByPointId(this.selected[1])
          // const pos = this.getShiftedExtendLinePos()
          const newLine = new Konva.Line({
            points: [extended[0][0], extended[0][1], s[0], s[1]],
            stroke: "grey",
            strokeWidth: 2,
            id: "paraLineNext"
          })
          this.watchingMouse.push("paraLineNext")
          this.$refs.lineLayer.getNode().add(newLine)
        } else {
          const line = this.getLineByLineId("paraLineNext")
          if (line) {
            line.remove()
          }
        }

        if (this.selected.length === 1 && ["circle"].indexOf(this.status) !== -1) {
          const center = this.getPointById(this.selected[0])
          const pos = this.getMousePos()
          const newCircle = new Konva.Circle({
            radius: this.getDistByPointPos(this.getCoordinateByPoint(center), pos),
            x: center.x(),
            y: center.y(),
            stroke: "grey",
            strokeWidth: 2,
            id: "mouseCircle",
            fillEnabled: false
          })
          this.watchingMouse.push("mouseCircle")
          this.$refs.circleLayer.getNode().add(newCircle)
        } else {
          const circle = this.getCircleByCircleId("mouseCircle")
          if (circle) {
            circle.remove()
          }
        }

        this.draw()
      }
    }
  }
</script>

<style scoped>

/*Disable blank scrollbar in Chrome. */
/*::-webkit-scrollbar {*/
/*  width: 0 !important;height: 0;}*/

#canvas {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#theory-list, #proof-context {
  display: inline-block;
  width: 25%;
  position: fixed;
  top: 48px;
  bottom: 0;
  left: 0;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 5px;
}

#theory-content {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#message, #status, #query {
  display: inline-block;
  width: 75%;
  height: 25%;
  left: 25%;
  position: fixed;
  top: 75%;
  bottom: 0;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}

#tool {
  display: inline-block;
  width: 75%;
  height: 5%;
  left: 25%;
  position: fixed;
  top: 70%;
  bottom: 0;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}

</style>