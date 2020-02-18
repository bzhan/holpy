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
          <b-dropdown-item href="#" @click="handleClickConstructMidpoint">MidPoint</b-dropdown-item>
          <b-dropdown-item href="#" @click="handleClickConstructCircle">Circle</b-dropdown-item>
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
      <h6>{{status}}</h6>
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
        if (this.status === "point") {
          this.lines.forEach(line => {
            let x1 = this.points[line.points[0]].x
            let y1 = this.points[line.points[0]].y
            let x2 = this.points[line.points[1]].x
            let y2 = this.points[line.points[1]].y
            window.console.log(this.getYbyLine(x1, y1, x2, y2, x), y)
            if (Math.abs(this.getYbyLine(x1, y1, x2, y2, x) - y) < 5 ||
                    Math.abs(this.getXbyLine(x1, y1, x2, y2, y) - x) < 5) {
              canAdd = false
            }
          })
          if (canAdd) {
            this.addAnchor(x, y)
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
        const anchor1 = this.$refs.stage.getNode().find('#' + id1)[0].getChildren()[0]
        const anchor2 = this.$refs.stage.getNode().find('#' + id2)[0].getChildren()[0]
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
          stroke: "black",
          strokeWidth: 2,
          id: id.toString(),
          draggable: true
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
                    let newX = this.$refs.stage.getNode().getPointerPosition().x
                    let newY = this.$refs.stage.getNode().getPointerPosition().y
                    let calX = this.getXbyLine(x1, y1, x2, y2, newY)
                    let calY = this.getYbyLine(x1, y1, x2, y2, newX)
                    if ((calX - newX) / newX < (calY - newY) / newY) {
                      const newPtId = this.addAnchor(calX, newY)
                      newLine.getAttr('points').push(calX, newY)
                      this.addPointToLine(info, newPtId, calX)
                    } else {
                      const newPtId = this.addAnchor(newX, calY)
                      newLine.getAttr('points').push(newX, calY)
                      this.addPointToLine(info, newPtId, newX)
                    }
                    this.$refs.lineLayer.getNode().draw()
                  }
                }
          )
        this.$refs.lineLayer.getNode().add(newLine)
        this.$refs.lineLayer.getNode().draw()
      },
      addPointToLine(info, id, x) {
        for (let i = 0; i < info.points.length; i ++) {
          if (x > info.points[i].x) {
            info.points.splice(i, 0, id)
            return 0
          }
        }
        info.points.push(id)
      },
      getYbyLine(x1, y1, x2, y2, newX) {
        return y1 + (y2 - y1) / (x2 - x1) * (newX - x1)
      },
      getXbyLine(x1, y1, x2, y2, newY) {
        return (newY - y1) / ((y2 - y1) / (x2 - x1)) + x1
      },
      getLineIdByAnchor(p1, p2) {
        for (let id in this.lines) {
          if (this.lines[id].points.indexOf(p1) !== -1 && this.lines[id].points.indexOf(p2) !== -1) {
            return id
          }
        }
        return null
      },
      addAnchor(x, y) {
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
        let info = {"name": name, "activated": false, "x": x, "y": y}
        this.points[id] = info
        const group = new Konva.Group({
          draggable: true,
          isDragging: false,
          id: id.toString()
        });
        const newCircle = new Konva.Circle({
          x: x,
          y: y,
          radius: 5,
          stroke: "black",
          strokeWidth: 2,
          fill: "red",
        })
        const newText = new Konva.Text({
          x: x + 5,
          y: y - 20,
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
            if (this.selected.length < 1) {
              this.addAnchorToSelected(id)
            } else {
              this.addAnchorToSelected(id)
              this.addLine(this.selected[0], this.selected[1])
              this.selected = []
              this.clearAnchorsActivation()
            }
          }
          else if (this.status === "midpoint") {
            info.activated = true
            if (this.selected.length < 1) {
              this.addAnchorToSelected(id)
            } else {
              this.addAnchorToSelected(id)
              const lineId = this.getLineIdByAnchor(this.selected[0], this.selected[1])
              const line = this.$refs.lineLayer.getNode().findOne('#' + lineId)
              const p1 = this.lines[lineId].points[0]
              const p2 = this.lines[lineId].points[this.lines[lineId].points.length - 1]
              const x1 = this.points[p1].x
              const y1 = this.points[p1].y
              const x2 = this.points[p2].x
              const y2 = this.points[p2].y
              let calX = (this.points[this.selected[0]].x + this.points[this.selected[1]].x) / 2
              let calY = this.getYbyLine(x1, y1, x2, y2, calX)
              const newPtId = this.addAnchor(calX, calY)
              line.getAttr('points').push(calX, calY)
              this.addPointToLine(this.lines[lineId], newPtId, calX)
              this.$refs.lineLayer.getNode().draw()
              this.selected = []
              this.clearAnchorsActivation()
            }

          }
        })

        group.on("dragmove", () => {
          info.x = group.x()
          info.y = group.y()
        })
        // group.on("dragend", this.handleDragEndAnchor)
        this.$refs.anchorLayer.getNode().add(group)
        this.$refs.anchorLayer.getNode().draw()
        return id
      },
      addAnchorToSelected(id) {
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
      updateObjects() {
        const anchorLayer = this.$refs.anchorLayer.getNode()
        // const lineLayer = this.$refs.lineLayer.getNode()
        this.points.forEach(point => {
          let node = anchorLayer.findOne('#' + point.id);
          node.x(point.x);
          node.y(point.y);
        })
      },
      clearAnchorsActivation() {
        let children = this.$refs.anchorLayer.getNode().getChildren()
        for (let i = 0; i < children.length; i ++) {
          children[i].getChildren()[0].strokeWidth(2)
        }
        this.$refs.anchorLayer.getNode().draw()
        for (let id in this.points) {
          this.points[id]['activated'] = false
        }
        this.$refs.anchorLayer.getNode().draw()
      }
    },
    watch: {
      status() {
        this.clearAnchorsActivation()
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