<template>
  <div align=left>
    <span class="keyword">theory</span>&nbsp;{{theory.name}}
    <br>
    <span class="keyword">imports</span>&nbsp;{{theory.imports.join(' ')}}
    <br><br>
    <span class="comment">{{theory.description}}</span>
    <br><br>
    <div v-for="(item, index) in theory.content" v-bind:key=index v-bind:item_id=index class="theory-items">
      <div v-if="item.ty === 'header'">
        <span class="header-item">{{item.name}}</span>
      </div>
      <div v-if="item.ty === 'type.ax'">
        <span class="keyword">type</span>&nbsp;
        <span class="item-text">{{item.name}}</span>
      </div>
      <div v-if="item.ty === 'def.ax'">
        <span class="keyword">constant</span>&nbsp;
        <span class="item-text">{{item.name}}</span> ::
        <span class="item-text" v-html="highlight_html(item.type_hl)"></span>
      </div>
      <div v-if="item.ty === 'type.ind'">
        <span class="keyword">datatype</span>&nbsp;
        <span class="item-text" v-html="highlight_html(item.type_hl)"></span> =
        <span v-for="(v, i) in item.constr_output_hl" v-bind:key=i>
          <br><span class="item-text indented-text" v-html="highlight_html(v)"></span>
        </span>
      </div>
      <div v-if="item.ty === 'def'">
        <span class="keyword">definition</span>&nbsp;
        <span class="item-text">{{item.name}}</span> ::
        <span class="item-text" v-html="highlight_html(item.type_hl)"></span>&nbsp;
        <span class="keyword">where</span>
        <br>
        <span class="item-text indented-text" v-html="highlight_html(item.prop_hl)"></span>
      </div>
      <div v-if="item.ty === 'def.ind'">
        <span class="keyword">fun</span>&nbsp;
        <span class="item-text">{{item.name}}</span> ::
        <span class="item-text" v-html="highlight_html(item.type_hl)"></span>&nbsp;
        <span class="keyword">where</span>
        <span v-for="(v, i) in item.rules" v-bind:key=i>
          <br><span class="item-text indented-text" v-html="highlight_html(v.prop_hl)"></span>
        </span>
      </div>
      <div v-if="item.ty === 'def.pred'">
        <span class="keyword">inductive</span>&nbsp;
        <span class="item-text">{{item.name}}</span> :: 
        <span class="item-text" v-html="highlight_html(item.type_hl)"></span>&nbsp;
        <span class="keyword">where</span>
        <span v-for="(v, i) in item.rules" v-bind:key=i>
          <br><span class="item-text indented-text" v-html="highlight_html(v.prop_hl)"></span>
        </span>
      </div>
      <div v-if="item.ty === 'macro'">
        <span class="keyword">macro</span>&nbsp;
        <span class="item-text">{{item.name}}</span>
      </div>
      <div v-if="item.ty === 'method'">
        <span class="keyword">method</span>&nbsp;
        <span class="item-text">{{item.name}}</span>
      </div>
      <div v-if="item.ty === 'thm'">
        <span class="keyword">theorem</span>&nbsp;
        <span class="item-text">{{item.name}}</span>:&nbsp;&nbsp;
        <a href="#" name="proof" style="font-style:italic" v-bind:style="{color:get_status_color(item)}">proof</a>
        <br>
        <span v-if="'prop_hl' in item">
          <span v-for="(line, i) in item.prop_hl" v-bind:key=i>
            <span class="item-text indented-text" v-html="highlight_html(line)"></span><br>
          </span>
        </span>
        <div v-if="'err_type' in item">
          <div v-if="typeof(item.prop) === 'string'">
            <span class="item-text indented-text">{{item.prop}}</span>
          </div>
          <div v-else>
            <span class="item-text indented-text" v-for="(line, i) in item.prop" v-bind:key=i>
              {{line}}<br>
            </span>
          </div>
          <pre class="error-text indented-text">{{item.err_str}}</pre>
        </div>
      </div>
      <div v-if="item.ty === 'thm.ax'">
        <span class="keyword">axiom</span>&nbsp;
        <span class="item-text">{{item.name}}</span>:
        <br>
        <span v-if="'prop_hl' in item">
          <span v-for="(line, i) in item.prop_hl" v-bind:key=i>
            <span class="item-text indented-text" v-html="highlight_html(line)"></span><br>
          </span>
        </span>
      </div>
    </div>
  </div>
</template>

<script>
export default {
  name: 'Theory',
  props: [
    "theory"
  ],

  methods: {
    // Mapping of colors.
    rp: function (x) {
      if (x === 0)
        return 'normal';
      if (x === 1)
        return 'bound';
      if (x === 2)
        return 'var';
      if (x === 3)
        return 'tvar';
    },

    // Convert a list of (s, color) to html form.
    highlight_html: function (lst) {
      var output = '';
      for (let i = 0; i < lst.length; i++) {
        output = output + '<span class="' + this.rp(lst[i][1]) + '">' + lst[i][0].replace(/ /g, '&ensp;') + '</span>'
      }
      return output
    },

    get_status_color: function (item) {
      if (item.proof === undefined) {
        return 'red';
      } else if (item.num_gaps > 0) {
        return 'chocolate';
      } else {
        return 'green';
      }
    }
  }
}
</script>

<style scoped>

input, textarea, .item-text {
    font-family: monospace;
}

.theory-items + div {
    margin-top: 10px;
    margin-bottom: 10px;
}

.keyword {
    font-weight: bold;
    color: #006000;
}

.comment {
    color: green;
}

.header-item {
    font-size: 14pt;
}

.indented-text {
    margin-left: 0.8em;
}

.error-text {
  color: red;
}

</style>
