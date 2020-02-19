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
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Constraint" left>
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
      <v-stage :config="stageSize" ref="stage" @click="handleClickLayer">
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
        midpoints: [],
        selected: []
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
            const p = this.$refs.anchorLayer.getNode().findOne('#' + id)
            const dist = Math.sqrt(Math.pow(x - p.x(), 2) + Math.pow(y - p.y(), 2))
            if (dist < 10) {
              canAdd = false
              break
            }
          }
        }
        if (canAdd) {
          if (this.status === "point") {
            this.addAnchor(x, y)
          }
          else if (this.status === "line") {
            let newId = this.addAnchor(x, y, true)
            this.addToSelected(newId)
            if (this.selected.length === 2) {
              this.addToSelected(newId)
              this.addLine(this.selected[0], this.selected[1])
              this.selected = []
              this.clearActivationAll()
            }
          }
          else if (this.status === "perpendicular") {
            if (this.selected.length === 0) {
              let newId = this.addAnchor(x, y, true)
              this.addToSelected(newId)
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
        let id = 100
        while (this.lines.hasOwnProperty(id)) {
          id += 1
        }
        let info = undefined
        if (x1 < x2) {
          info = {"points": [id1, id2], "activated": false}
        } else {info = {"points": [id2, id1], "activated": false}}
        this.lines[id] = info
        const newLine = new Konva.Line({
          points: [x1, y1, x2, y2],
          stroke: "grey",
          strokeWidth: 2,
          id: id.toString(),
          // draggable: true
        })
        newLine.on("mouseover", () => {
          document.body.style.cursor = 'pointer'
          newLine.strokeWidth(4)
          this.$refs.lineLayer.getNode().draw()
        })
        newLine.on("mouseout", () => {
          if (info.activated === false) {
            document.body.style.cursor = 'default'
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
                    const newX = this.$refs.stage.getNode().getPointerPosition().x
                    const newY = this.$refs.stage.getNode().getPointerPosition().y
                    const r = this.getMinDistPointToSeg([newX, newY], [x1, y1], [x2, y2])
                    const minDist = r[0]
                    const foot = r[1]
                    if (minDist < 5) {
                      const newPtId = this.addAnchor(foot[0], foot[1])
                      newLine.getAttr('points').push(foot[0], foot[1])
                      this.addPointToLineList(info, newPtId, foot[0])
                    }
                    this.$refs.lineLayer.getNode().draw()
                  }
                  else if (this.status === "intersection") {
                    info.activated = true
                    this.addToSelected(id)
                    if (this.selected.length === 2) {
                      this.addToSelected(id)
                      this.addLine(this.selected[0], this.selected[1])
                      this.selected = []
                      this.clearActivationAll()
                    }
                  }
                }
          )
        this.$refs.lineLayer.getNode().add(newLine)
        this.$refs.lineLayer.getNode().draw()
      },
      addPointToLineList(info, id, x) {
        for (let i = 0; i < info.points.length; i ++) {
          if (x > info.points[i].x) {
            info.points.splice(i, 0, id)
            return 0
          }
        }
        info.points.push(id)
      },
      getYbyLine(x1, y1, x2, y2, newX) {
        return y1 + ((y2 - y1) / (x2 - x1)) * (newX - x1)
      },
      getXbyLine(x1, y1, x2, y2, newY) {
        return (newY - y1) / ((y2 - y1) / (x2 - x1)) + x1
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
      getPointById(id) {
        return this.$refs.anchorLayer.getNode().findOne('#' + id)
      },
      getCoordinateById(id) {
        return this.getCoordinateByPoint(this.getPointById(id))
      },
      getPedalCoordinatePointToSeg(pair, pair1, pair2) {
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
        let xx, yy
        if (param < 0 || param > 1) {
          xx = Infinity
          yy = Infinity
        } else {
          xx = x1 + param * C
          yy = y1 + param * D
        }
        return [xx, yy]
      },
      getMinDistPointToSeg(pair, pair1, pair2) {
        const x = pair[0]
        const y = pair[1]
        const pedalPos = this.getPedalCoordinatePointToSeg(pair, pair1, pair2)
        const dx = x - pedalPos[0]
        const dy = y - pedalPos[1]
        return [Math.sqrt(dx * dx + dy * dy), pedalPos];
      },
      addAnchor(x, y, activated) {
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
          info = {"name": name, "activated": true, "x": x, "y": y}
        } else {
          info = {"name": name, "activated": false, "x": x, "y": y}
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
          fill: "red",
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
            if (this.selected.length === 2) {
              this.addLine(this.selected[0], this.selected[1])
              this.selected = []
              this.clearActivationAll()
            }
          }
          else if (this.status === "midpoint") {
            info.activated = true
            this.addToSelected(id)
            if (this.selected.length === 2) {
              const lineId = this.getLineIdByPointId(this.selected[0], this.selected[1])
              if (lineId) {
                const line = this.$refs.lineLayer.getNode().findOne('#' + lineId)
                const p1 = this.$refs.anchorLayer.getNode().findOne(
                        '#' + this.selected[0])
                const p2 = this.$refs.anchorLayer.getNode().findOne(
                        '#' + this.selected[1])
                let calX = (p1.x() + p2.x()) / 2
                let calY = this.getYbyLine(p1.x(), p1.y(), p2.x(), p2.y(), calX)
                const newPtId = this.addAnchor(calX, calY)
                line.getAttr('points').push(calX, calY)
                this.addPointToLineList(this.lines[lineId], newPtId, calX)
                this.midpoints.push([newPtId, p1, p2])
                this.$refs.lineLayer.getNode().draw()
            }
              this.selected = []
              this.clearActivationAll()
            }
          }
          else if (this.status === "perpendicular") {
            info.activated = true
            this.addToSelected(id)
            if (this.selected.length === 3) {
              const perpTo = this.getLineIdByPointId(this.selected[1], this.selected[2])
              if (!perpTo) {
                this.clearActivationAll()
                return
              }
              const endPointIds = this.getEndPointsIdByLineId(perpTo)
              const r = this.getPedalCoordinatePointToSeg(this.getCoordinateById(this.selected[0]),
                      this.getCoordinateById(endPointIds[0]), this.getCoordinateById(endPointIds[1]))
              if (r[0] === Infinity) {
                this.clearActivationAll()
                return
              }
              const footId = this.addAnchor(r[0], r[1])
              this.addLine(this.selected[0], footId)
              this.clearActivationAll()
            }
          }
        })

        group.on("dragmove", () => {
          info.x = group.x()
          info.y = group.y()
          this.updateObjects()
        })
        // group.on("dragend", this.handleDragEndAnchor)
        this.$refs.anchorLayer.getNode().add(group)
        this.$refs.anchorLayer.getNode().draw()
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
      updateObjects() {
        const anchorLayer = this.$refs.anchorLayer.getNode()
        // const lineLayer = this.$refs.lineLayer.getNode()
        for (let id in this.points) {
          let node = anchorLayer.findOne('#' + id)
          node.x(this.points[id].x)
          node.y(this.points[id].y)
        }
      },
      clearActivationAll() {
        this.selected = []
        let allPoints = this.$refs.anchorLayer.getNode().getChildren()
        let allLines = this.$refs.lineLayer.getNode().getChildren()
        for (let i = 0; i < allPoints.length; i ++) {
          allPoints[i].getChildren()[0].strokeWidth(2)
        }
        for (let i = 0; i < allLines.length; i ++) {
          allLines[i].strokeWidth(2)
        }
        for (let id in this.points) {
          this.points[id]['activated'] = false
        }
        for (let id in this.lines) {
          this.lines[id]['activated'] = false
        }
        this.$refs.anchorLayer.getNode().draw()
        this.$refs.lineLayer.getNode().draw()
      }
    },
    watch: {
      status() {
        this.clearActivationAll()
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